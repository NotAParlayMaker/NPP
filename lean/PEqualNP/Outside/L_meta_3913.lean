import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3913_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero∧a≠one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
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
theorem Live.zeroSet {T t S} (h : Live T 0 t S) : S={T}:=by
  have hh:=h (fun k _ W => k=0 → W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {k t S} (h : Live target k t S) : t ≤ k∧S.card+t ≤ k+1:=by
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
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma bin_laws (a : Sig) :
    bin false a one=a∧bin true a zero=a ∧
    bin false a zero=zero∧bin true a one=one ∧
    bin false a a=a∧bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma neg_laws : neg zero=one∧neg one=zero:=by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a=zero∨a=one∨a ∈ w∧proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w,proper a∧z=neg a) ∨
  (∃ d a b,a ∈ w∧b ∈ w∧proper a∧proper b∧a≠b∧z=bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b)∨witness w (bin d a b):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws b
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
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    represented w (gv w g)∨witness w (gv w g):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩:=h
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a)∨witness w (neg a):=by
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
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b:=witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b:=witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z∨witness w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧Live target k' t' S'∧∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w∨a=z:=by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (neg a)
        have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U:=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U):=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧Live target k t S∧∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩:=pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
private lemma bit_zero (i) : bit i zero=false:=by simp [bit,zero]
private lemma bit_one (i) : bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
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
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type):=R → Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat:=(xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool∨Constant v
def supply {R} (pool xs : List (Wire R)):=∀ a ∈ xs,Available pool a
def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop:=fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
theorem Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots:=fun M start one two => @start
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank):=fun M start one two => @one p bank a (h0 M start one two) h1
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank):=fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
theorem Reach.induct {R} {roots : List (Wire R)} {M : (Nat → List (Wire R) → Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},Reach roots p bank → M p bank → Available bank a → M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),Reach roots p bank → M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank∧M p bank)
  (⟨@Reach.start R roots  ,@start  ⟩)
  (@fun p bank a h0 h1 => ⟨@Reach.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
  (@fun p bank a b op h0 h1 h2 => ⟨@Reach.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
theorem Reach.recurse {R} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)) (proof : Reach roots p bank),Prop}
  (start : M 0 roots (@Reach.start R roots  ))
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a),M (p+1) (inv a :: bank) (@Reach.one R roots p bank a h0 h2))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a) (h3 : Available bank b),M (p+1) (combine op a b :: bank) (@Reach.two R roots p bank a b op h0 h2 h3))
  {p bank} (h : Reach roots p bank) : M p bank h:=by
  have r:=Reach.induct (M:=fun p bank => ∀ hh : Reach roots p bank,M p bank hh) h
    (fun  _ => @start  )
    (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
    (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
  exact r h
def kept {α : Type} (save : Bool) (x : α) (xs : List α):=if save then x::xs else xs
def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop:=fun s ws =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → M s xs → M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),M s (inv a :: kept save a rest) → M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) →
  M s ws
theorem Run.stop {R} {goal : Wire R}   : Run goal 0 [goal]:=fun M stop perm one two => @stop
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
theorem Run.induct {R} {goal : Wire R} {M : (Nat → List (Wire R) → Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → Run goal s xs → M s xs → M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),Run goal s (inv a :: kept save a rest) → M s (inv a :: kept save a rest) → M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),Run goal s (combine op a b :: kept ka a (kept kb b rest)) → M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws∧M s ws)
  (⟨@Run.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
theorem Run.recurse {R} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)) (proof : Run goal s ws),Prop}
  (stop : M 0 [goal] (@Run.stop R goal  ))
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) (ih : M s xs h1),M s zs (@Run.perm R goal s xs zs h0 h1))
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) h0),M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) h0),M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
  {s ws} (h : Run goal s ws) : M s ws h:=by
  have r:=Run.induct (M:=fun s ws => ∀ hh : Run goal s ws,M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a+mass xs:=by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs):=by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a):=by
  obtain ⟨v,rfl⟩:=h
  exact ⟨!v,rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b):=by
  obtain ⟨v,rfl⟩:=h
  obtain ⟨w,rfl⟩:=g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a∨Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b):=by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next,Reach roots q next∧Available next (inv a) ∧
        (∀ v,Available bank v → Available next v)∧q+cost a ≤ p+1+cost (inv a):=by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩
theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next,Reach roots q next∧Available next (combine op a b) ∧
        (∀ v,Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b):=by
  classical
  by_cases c : Constant a∨Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a:=fun h => c (Or.inl h)
    have cb : ¬Constant b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a∨x∈xs:=by cases k <;> simp_all [kept]
theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next,Reach roots q next∧Available next goal∧q+mass ws ≤ p+s:=by
  classical
  induction h using Run.recurse generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a (kept kb b rest) ka
    have hlen':=mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)):=by
  cases k <;> simp [kept]
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)):=by
  induction h using Run.recurse with
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
    (hl : ∀ q bs,Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L+mass (ws.map (restrictRows rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩:=contraction nc (restrict_run rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f)=f r:=by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v)=v:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f)=f:=by
  funext r
  exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a)=inv (observe a):=by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b)=combine d (observe a) (observe b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f=kept d (f a) (l.map f):=by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup:=by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [kept]
theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset=S) : Run (observe T) k (v.map observe):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=kept save a rest
    have er : rest.toFinset=U.erase a:=by simp [rest]
    have hm : a ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have ht : tail.toFinset=U:=by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=kept_nd save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=kept kb b rest
    let tail:=kept ka a mid
    have er : rest.toFinset=(U.erase a).erase b:=by simp [rest]
    have ar : a ∉ rest:=by simp [rest]
    have br : b ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have bm:=kept_nd kb b rest hr br
    have am : a ∉ mid:=by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd:=kept_nd ka a mid bm am
    have ht : tail.toFinset=U:=by
      change (kept ka a (kept kb b rest)).toFinset=U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f)=neg (table f):=by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g)=bin d (table f) (table g):=by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]
theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a)∨witness w (neg a):=by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z∨witness w z) (hs : ∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1∧Live T k' t' S'∧∀ a ∈ S',a ∈ w:=by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S,a ∈ bank.map table) :
    ∃ l v U,l ≤ p+k∧Live T l v U∧∀ a ∈ U,a ∈ roots.map table:=by
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S,k ≤ p∧Live T k t S∧∀ a ∈ S,a ∈ roots:=by
  have hm:=available_rep hit
  rw [table_observe] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩:=reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T≠bit s T) : ∃ a ∈ S,bit r a≠bit s a:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S,v ∈ roots) (r s : Row) (diff : bit r T≠bit s T)
    (isolated : ∀ v ∈ roots,v≠a → bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩:=live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def oldSeed : Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed : Sig:=inputs.getD 0 zero ||| inputs.getD 4 zero
def sample (r : Row) (j : Fin 9):=bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
theorem edge_table : ∀ r : Row,bit r graph=edge (sample r):=by decide +kernel
theorem seed_table : ∀ r : Row,bit r seed=(sample r 0||sample r 4):=by decide +kernel
theorem graph_proper : proper graph:=by unfold proper; decide +kernel
theorem seed_nonzero : seed≠zero:=by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero)=inputs:=rfl
theorem sampled (r : Row) : List.ofFn (sample r)=inputs.map (bit r):=by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false:=by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l,execute gs ws=ws ++ l:=by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩:=ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def neighbor (i : Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w==inputs.getD i.val zero ||
      bit (absentRow i) w==bit (presentRow i) w)=true:=by decide +kernel
theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S,v ∈ inputs++[seed]) :
    S=inputs.toFinset∨S=(inputs++[seed]).toFinset:=by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S:=by
    have cut:=seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S:=by
    intro v hv
    have hm:=List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩:=hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx:=List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx:=sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed
theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool,(C.wires (List.ofFn y)).getD 9 false=(y 0||y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C=edge) (small : C.size ≤ 15) :
    ∃ k t,k ≤ 14∧(Live graph k t inputs.toFinset∨Live graph k t (inputs++[seed]).toFinset):=by
  have headEq : (execute C.gates inputs).getD 9 zero=seed:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out:=get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn:=out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g=seed:=by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero=seed at headEq
      obtain ⟨l,hl⟩:=exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs,gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧gate.inputs.length≤2:=by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩:=extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15:=by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)
def rename (f : Row → Row) (a : Sig):=table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a)=bit (f r) a:=bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a)=restrictRows f (observe a):=by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a)=neg (rename f a):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a))=bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b)=bin d (rename f a) (rename f b):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b))=bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f):=by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero=zero∧rename f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)):=by
  have inj:=rename_inj f onto
  obtain ⟨fz,fo⟩:=rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.recurse with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
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
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank,Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row,bit r T≠bit s T∧∀ v ∈ roots,v≠a → bit r v=bit s v
theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots,Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1):=by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩:=reach_live hp h ha
  have he : roots.toFinset=S:=by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:=essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v):=by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v:=by
    have avail : Available ([] : List (Wire Row)) (observe v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b)=mass a+mass b:=by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs,Constant x) :
    mass xs=xs.length:=by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T=G)
    (covered : ∀ a ∈ roots,Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles,Essential T roots a)
    (constant : ∀ a ∈ singles,Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L+singles.card):=by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live pT hh ha
  have subS : singles ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:=necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front:=singles.toList ++ (S \ singles).toList
  have nd : front.Nodup:=by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':=list_run run front nd fe
  have gc : restrictRows r (observe T)=observe G:=(observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)):=by
    simp only [front,List.map_append,mass_append]
    let xs:=(singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs,Constant v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs+_
    rw [sz]
    omega
  omega
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset:=by
  classical
  intro k t hk h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    have mem : T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      have nk:=kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len : (childOne ws a keep).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup:=by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_
      simp [ke]
    have sc:=(live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true∧bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws=BitVec.allOnes width:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩:=live_row_difference h (show bit (r i) T≠bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩:=mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n:=by
  apply cover_sound h rfl correct
  intro hh
  have eq:=of_decide_eq_true hh
  have bound:=(live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank,Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig):=a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m:=masked d a
  m==zero||m==d||(pool.map (masked d)).any (fun v => v==m)
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=masked d b) :
    restrictRows f (observe a)=restrictRows f (observe b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=zero) : restrictRows f (observe a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=d) : restrictRows f (observe a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool,Available bank (restrictRows f (observe a))
theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r,bit (f r) d=true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a=true) : Available bank (restrictRows f (observe a)):=by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice:=Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1&&(c.1==2||availableB d pool c.2.2)
theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r,bit (f r) d=true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c=true) :
    ∃ next,Reach roots (q+1) next∧poolSupply f next (choiceVal c :: pool):=by
  have ok : availableB d pool c.2.1=true∧(c.1==2||availableB d pool c.2.2)=true:=by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha:=availableB_sound dom hs ok.1
  let z:=restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank):=by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz':=Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w)=combine b (restrictRows f v) (restrictRows f w):=by cases b <;> rfl
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
theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r,bit (f r) d=true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs=some result) :
    ∃ next,Reach roots (q+cs.length) next∧poolSupply f next result:=by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩:=pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩:=ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig):=masked d a==zero||masked d a==d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r,bit (f r) d=true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)):=by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)):=by
        have hh : masked d a=zero∨masked d a=d:=by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d))&&ws.all (availableB d pool)
theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs=some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws=true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
  obtain ⟨bank,hr,hs⟩:=makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:=cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b:=projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo:=count_constants dom ws
  have hu:=ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move:=Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row:=Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig):=(m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val)=bit (shifted d r) a:=by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y : Bool) : (p&&x||!p&&y)=(if p then x else y):=by cases p <;> simp
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a)=bit (rowMove m r) a:=by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row):=ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig):=ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a)=bit (movedRow ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a=rename (movedRow ms) a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig):=w==zero||w==one||roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w=true) :
    Available (roots.map observe) (observe w):=by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T==G&&raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G=true) :
    rename (movedRow ms) T=G ∧
    ∀ a ∈ raw,Available (base.map observe) (observe (rename (movedRow ms) a)):=by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G=true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G=true)
    (all : movedWord ms d=one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  have obs : restrictRows (movedRow ms) (observe T)=observe G :=
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
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs=true) : Essential T roots a:=by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)
theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs=true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:=essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound:=(live_size run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G&&checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1==zero||movedWord ms a.1==one)
theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs=true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩:=map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat):=(selected m).map Prod.snd
def vertex (m j : Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x:=vertex m
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
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig):=T != zero&&T != one
theorem proper_of (T : Sig) (h : properB T=true) : proper T:=by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs:=graphPairs m hints
  properB (graphGoal m)&&checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L=true) :
    Lower (vars m) (graphGoal m) L:=by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  let count:=(xs.map Prod.fst).toFinset.card
  properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs&&decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior=true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩:=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  change (((properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old)&&properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps=true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L:=by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q):=by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1==q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1==q) e=true:=List.find?_some (p:=fun a : Nat × Nat => a.1==q) (a:=e) h
    have eq : e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (c : BoundPool) : Sig:=c.1
abbrev BoundPool.bound (c : BoundPool) : Nat:=c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat:=c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig:=c.2.2.2
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r,bit (f r) c.domain=true)∧¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws,Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank∧poolSupply f bank c.wires∧True
theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs=some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩:=by
  obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
  obtain ⟨bank,hr,hs⟩:=makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest,availableB c.domain c.wires a=true)
    (buy : if paid then choiceOK c.domain c.wires choice=true
       else availableB c.domain c.wires (choiceVal choice)=true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid
  let ws:=choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n=c.paid+paid.toNat) : False:=by
    have covered : supply out ((ws.map observe).map (restrictRows f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
      exact zs _ ha
    have b:=projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm:=count_constants dom ws
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
    obtain ⟨out,hr,hc⟩:=pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z:=choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires))&&(!extra||choiceOK c.domain c.wires op)
theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op=true) :
    Impossible T k (choiceVal op::rest).toFinset:=by
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
    (h : materialize raw cs d L=some c) : ValidPool raw T c:=by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h
    change some _=some c at h
    injection h with h
    subst c
    exact build_valid slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val=bit (r i) v:=by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals:=(ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i,bit (r i) T=true∧bit (s i) T=false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s):=by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor):=x.2=pairSig r s x.1
def dneg (x : Decor) : Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b)=if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x):=by
  change x.2=_ at h
  simp only [faithful,dneg,pairSig,ofRows_neg,h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y):=by
  change x.2=_ at hx
  change y.2=_ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor:=(zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j=(ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j=(ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws,faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws,faithful r s v) :
    ∀ v ∈ decodeBank n bits ws,faithful r s v:=by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:=List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
theorem coordinate1 : ∀ r : Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
theorem coordinate2 : ∀ r : Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
theorem coordinate3 : ∀ r : Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
theorem coordinate4 : ∀ r : Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
theorem coordinate5 : ∀ r : Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
theorem coordinate6 : ∀ r : Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
theorem coordinate7 : ∀ r : Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
theorem coordinate8 : ∀ r : Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
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
    bit (asRow cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9∧a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q,faithful (asRow p) (asRow q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:=selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m)=(liftGoal m v).getLsbD i.val:=by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val=((if m.testBit j then v j else 0) : Bits).getLsbD i.val:=bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v,faithful r s a) :
    (coverage d v).1=covered d (pairSig r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1)=column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)):=by
  cases keep
  · change (coverage d (ws.erase a)).1=takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)):=by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1=takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b : List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws:=choiceVal op::rest
  (links (keySet ws)).any (sameWords ws)||pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair:=Cov × Cov
def preCov (ws : List Decor) : CovPair:=(coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool):=if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d=coverage d ws:=by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb:=by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor):=codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice:=(op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1=choiceVal (movedChoice op a b):=by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b):=by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len>cap then true else
    let d:=len==cap
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb=true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz:=(live_size h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep:=cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap:=by omega
  rw [ce] at sep
  let d:=child.length==cap
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap)=(child.length==cap):=by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length=cap)) (pairSig r s) child=BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by simp [sep]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  have val:=moved_full op a b
  change z.1=_ at val
  change Live T k t child.toFinset at h
  have nd':=ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false&&evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false&&testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs&&testAll ctx bs
theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
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
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true∨testPair ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d=true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v↔(w=a∧k=true)∨w∈v:=by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k↔w∈v∧(w≠a∨k=true):=by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst∧(v≠a.1∨ka=true)∧(un=true∨v≠b.1∨kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (delOne_sub ws a ka)
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
    (moveFront ws 2 a a keep keep).toFinset=(childOne (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset=(childTwo v b a d kb ka).toFinset:=by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws=true) :
    Impossible T cap (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap:=by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d=true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move):=inputs.all (fun a => movedWord p (movedWord q a)==a)
theorem composed_id {p q} (h : composedOK p q=true) (r : Row) :
    movedRow q (movedRow p r)=r:=by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T==T)&&composedOK p p.reverse&&composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run:=live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def IndexTree (α : Type):=List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α:=xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α:=List.append a b
def IndexTree.read {α} (tree : IndexTree α) (i : Nat):=(show List α from tree)[i]?
def IndexTree.values {α} (tree : IndexTree α) : List α:=tree
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
def Forest:=(Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat:=c.1
def Forest.cap (c : Forest) : Nat:=c.2.1
def Forest.samples (c : Forest) : Nat → Bits × Bits:=c.2.2.1
def Forest.cols (c : Forest) : IndexTree ColumnInfo:=c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat):=c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat → Packing:=c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat → Nat → Option (Nat × Nat):=c.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:=by
  have base:=raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha
def targetOf (g : Forest):=chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m)=(chartSamples m v).getLsbD i.val:=by
  by_cases e : m=1023
  · have u:=asRow_bit v i (0 : Fin 9)
    have w:=asRow_bit v i (1 : Fin 9)
    have h:=bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val=(v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val=(v 1).getLsbD i.val at w
    have seedEq : oldSeed=inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p=BitVec.allOnes 768) (hq : chartSamples m q=0) :
    properPairs (chartGoal m) (asRow p) (asRow q):=by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1==1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def storedDepth (_g : Forest) (depth : Nat):=depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw:=wiresOf g
  let (_,depth,_,_,_,_,_,data):=g.levels k
  let len:=10*storedDepth g depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i*width) width
  let stored:=recp &&& ((1 <<< len)-1)
  let ops:=stored
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid=some c) :
    ValidPool (vars g.mask) (targetOf g) c:=by
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
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (earlier : ∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair=some out) :
    Impossible (targetOf g) k out.toFinset:=by
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
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let values:=ws.map Prod.fst
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup&&!(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1,Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i=true) : Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN:=checked.1.1
  have hT : targetOf g ∉ stateSet g k i:=by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0:=by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset=S at h
    rw [h.zeroSet] at he
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n)&&block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true:=by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true:=by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1=true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2)==0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : checkedTables g top) :
    ∀ k ≤ top,∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset:=by
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
  decide (i < (g.levels k).1)&&sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws=true) : Impossible (targetOf g) k ws.toFinset:=by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask)=true) (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem lower_discard {g prior ci hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior=true)
    (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2)=true) :
    Known (extendKnown old L relabels):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known []:=by simp [Known]
def lanePlace (v : Nat) (upper : Nat):=2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v=lanePlace (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v=lanePlace (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v=lanePlace (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs=combineLanes (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs=combineLanes (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs=combineLanes (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat=combineLanes (fun _ => a) xs:=by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed : Nat):=((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i)=true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i:=by omega
      have ge : ¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne : a.toNat≠2^768-1:=by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
    have hi' : i < xs.length+1:=hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769:=by omega
      have di : 769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig:=Nat × Nat
abbrev PackedCov:=Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs)=combineLanes (fun x => column d (s x)) xs:=by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat):=c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a:=contextWire c i
  let b:=contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1==0)||f x)&&onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0:=by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1≠0:=by
        intro he
        have at0:=congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:=Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat):=b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i=packedSig (fun c => (contextWire c i).2) xs:=by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero||m==p.domain||(p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x=availableMasked p (masked p.domain x):=rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p+constantLoss p a keep:=by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un||kb) ≤
    (opKeep un ka kb a b ws).countP p:=by
  have h1:=lossBound p ws a ka
  have h2:=lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool:=BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p:=s.1
  let un:=op==2
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let z:=choiceVal (movedChoice op a b)
  let zm:=masked p.domain z
  let zc:=isMaskedConstant p.domain z
  let cm:=s.2.1 - constantLoss const a ka - constantLoss const b (un||kb)+zc.toNat
  let free:=zc||zm==masked p.domain a.1||zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true:=by
  let z:=choiceVal (movedChoice op a b)
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let free:=isMaskedConstant p.domain z||masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest:=opKeep (op==2) ka kb a b ws
  have ck:=keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav:=List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true:=by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat:=by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true:=by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const+if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true:=by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1:=by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  have closed:=fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length∧j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true:=by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n-(if ka then 0 else 1)-(if un||kb then 0 else 1))
  if len>k then true else
    let d:=len==k
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true:=by
  let len:=1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d:=len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)):=by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (makeBatch k n xs) i
    let b:=laneWire (makeBatch k n xs) j
    let cov:=if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.1 d) xs:=by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a=_:=laneWire_at k n xs hi
    have cb : b=_:=laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f:=batchMove b xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false&&batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0&&batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js&&batchRows b xs js
theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true:=by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true:=by
  have all:=batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q])=xs[q].2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T : Sig) (c : NodeContext) :=
  let ws:=c.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i=(prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)):=rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat),start ≤ i → i < start+n → nodeVerified g k i=true) :
    block g k start n=true:=by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar&&prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs:=contexts g k start n
  let b:=makeBatch k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true:=by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:=List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true:=by
  let xs:=contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true:=by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok:=rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true:=by
  apply makeBlock
  intro i lo hi
  let xs:=contexts g k start n
  have hm : contextOf g k i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ha : xs[q].2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d∧boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true:=by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v:=rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true∧boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d∧cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true:=by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v:=block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d∧listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat:=0xf
def g15l3 : Packing:=(1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo:=(.leaf [])
def g15autos : Array (List Nat):=Array.mk [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest:=⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat:=0x84001e90fd02fd01fa00
def g31l5 : Packing:=(3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat:=0x11a20bf
def g31l6 : Packing:=(1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest:=⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo:=(.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat):=Array.mk [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest:=⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits):=Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo:=(.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat):=Array.mk [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest:=⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits):=Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo:=(.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat):=Array.mk [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest:=⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat:=0x120ff
def g111l6 : Packing:=(1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits):=Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat):=Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest:=⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits):=Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo:=(.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat):=Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest:=⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat:=0x82000f487f40bfa03fa00
def g189l6 : Packing:=(3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat:=0x1f5859bf
def g189l7 : Packing:=(1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits):=Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest:=⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits):=Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo:=(.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat):=Array.mk [[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest:=⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat:=0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat:=0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat:=0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat:=0x2c
def g191d6 (i : Nat) : Nat:=0x47d6448788a00
def g191l6 : Packing:=(1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat:=0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing:=(28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat:=0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing:=(100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat:=0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing:=(12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat:=0x1f3c11ff
def g191l10 : Packing:=(1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits):=Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
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
def g191 : Forest:=⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits):=Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo:=(.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat):=Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest:=⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits):=Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo:=(.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest:=⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat:=0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat:=0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat:=0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat:=0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat:=0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing:=(25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat:=0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing:=(91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat:=0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing:=(41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat:=0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing:=(6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat:=0x11b280e4ff
def g383l12 : Packing:=(1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits):=Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
def g383 : Forest:=⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1:=size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat):=[]
def known3:=extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3:=extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2:=size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat):=[]
def known7:=extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7:=extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true:=by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1=true:=s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0=true)
  · exact (rfl : block g15 1 0 0=true)
  · exact (rfl : block g15 2 0 0=true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15:=extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15:=extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3:=size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat):=[]
def known45:=extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45:=extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3:=size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat):=[]
def known51:=extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51:=extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true:=by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3=true:=(@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true:=by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1=true:=s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact (rfl : block g31 4 0 0=true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31:=extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31:=extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47:=extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47:=extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55:=extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55:=extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63:=extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63:=extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1=true:=s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact (rfl : block g111 5 0 0=true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111:=extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111:=extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119:=extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119:=extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3=true:=(@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1=true:=s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0=true)
  · exact (rfl : block g189 1 0 0=true)
  · exact (rfl : block g189 2 0 0=true)
  · exact (rfl : block g189 3 0 0=true)
  · exact (rfl : block g189 4 0 0=true)
  · exact (rfl : block g189 5 0 0=true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189:=extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189:=extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5:=size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat):=[]
def known250:=extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250:=extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127:=extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127:=extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1=true:=s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28=true:=(@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100=true:=(@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12=true:=(@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1=true:=s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0=true)
  · exact (rfl : block g191 1 0 0=true)
  · exact (rfl : block g191 2 0 0=true)
  · exact (rfl : block g191 3 0 0=true)
  · exact (rfl : block g191 4 0 0=true)
  · exact (rfl : block g191 5 0 0=true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191:=extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191:=extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251:=extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251:=extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255:=extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255:=extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25=true:=(@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true:=by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91=true:=(@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true:=by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41=true:=(@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6=true:=(@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true:=by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1=true:=s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0=true)
  · exact (rfl : block g383 1 0 0=true)
  · exact (rfl : block g383 2 0 0=true)
  · exact (rfl : block g383 3 0 0=true)
  · exact (rfl : block g383 4 0 0=true)
  · exact (rfl : block g383 5 0 0=true)
  · exact (rfl : block g383 6 0 0=true)
  · exact (rfl : block g383 7 0 0=true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383:=extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat:=0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat:=0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat:=(if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat:=0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat:=0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat:=0x202e0
def deadsamples : Array (Bits × Bits):=Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo:=(.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest:=⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def oP7F (i : Nat) : Nat:=0x3908101b87ddb242f00a43bf2e33201e8d06a130705522e55324520c84ebccc09b6e1b4acc1229064275e6604db54da566091483017af63026daa6d333048a4101797f8c136d52659a724d20
def oP7 : Packing:=(5,8,7,0,0,7,0,oP7F)
def oH7F (i : Nat) : Nat:=0x300c00009809818820
def oH7 (h : Nat) : Option (Nat × Nat):=lookupWord 5 5 3 11 3 4 oH7F h
def oP8F (i : Nat) : Nat:=(if i<1 then 0xc91483ed413048553615a724520cb593712154d8569c9148385e4cb48583655a724520e17932d216119569c9148325e4dc4859569e8824520c4bd7598132d5366091482c770eb4c1816959824520d0dd36d8160da56609148343758136dc36959824520919f798db70da5660914834374db605c86959824520d0dd604db54da566091482467de636d536959824520c0fd604db70da5660914834374db605856959824520e17531d8168db56609148346e4db605526999824520d0bd604db54da66609148206fdec36d536999824520d0bd36d81615a66609148344f4d7605b56999824520913f798db54da7660914838754c5605a36dd9824520c1dd37181695b7660914838674c5605a66dd9824520f8d232530549536a091482a771e0361c5245a124d20a9d9788d87149168493482a755e3361c5245a124d20a9cd790d87149168493482a675e6361c5245a124d20a95d79cd87149168493483a7c1a0605c32455224d20e9b868181718915489348385d9a76c1c32448524d20e15e69db0714912149348384f9a76c1c62448524d20d1f8749b0245a12149348347b1d46c0916848524d20d0fc761b0245a1214934834771b0754916848524d20d1d96c9d5245a1214934834735b4754916848524d2091f9789db245a12149348247b5e476c916848524d20d15769dd5245b32149348344dda7758916cc8524d20c17769ddc245b321493482c7c5e2245a16cc8524d20b1e579091685b321493482c755e5245a16cc8524d20b0f57a091685b32149348245dde7365a16cc8524d20d13769dd3245b621493483447da7754916d88524d20c13f69ddc245b621493482c6e5e2245a16d88524d20b1ad79091685b621493482c675e5245a16d88524d20b0bd7a091685b621493482c5e5e2245a16dc8524d20b16d79091685b721493482c575e5245a16dc8524d20b07d7a091685b72149348305ddc774c916e88524d20c1dd705d5245ba21493483057dc7754916e88524d20c13f71dd6245ba2149348205fde7770916e88524d20f13969cb15496565893483c671a02c5656159624d20e19d718b1615a565893482a579e0361c5245a724d20a95d784d87149169c93482a56de2361c5245a724d20a95778cd87149169c93482a53de4361c5245a724d20a91f798d87149169c93482857deb361c5245a724d20d971605d32455269c9348364e58175891549a724d20c93d360c15959669c93483a474c159585659a724d2091ed790db545a16609348246bde436d516999824d20916f790db545a76609348363c58174c91549a824d20d8b9605d6245526a09348306f4db30565659a824d20e89d30565615966a0934838748cb4c15254d9824d20e17132d218cd9569c9148385a4cb48644655a724520c87937121655a7a209148305e4c136d52659a724d20 else 0xcc10000001bc20000000000000101e08000407820000ba90807e10597080f0acb8081bc50a78a101d42e5c040acc04000000000072100002e0058401c840017040390805c00b080056a42017002c200dc205714200019a9080de1000000000e0304000000000000000000000000000000000000000000024b217818203a84000000000204a1ee04bef86bb6080000010c20800310b38a1671429e287bb690bc0521d14a033f27bcf29db36a6acd099731a60cbc96f2ca56ca894724245c869031ba34c648bf1321cc34827001fdbe87aaf09d7baa72ee49c6b88706df9bcb746c2d71abb36646c7985af85aeb4966aba532a1940a6e4d29912fa4c4728d117a2a44a8810da164067f8fc9f43de7a8f29e03b6758e89cc38e708de9b83666b8d49a433e668ca990316618c097c2ee5c8b69682c6578ac9542824b88d916222430839021fa3e0798d217e2b0538a213a260498800f61a02a84205e003ae4930549c62e55324d20f3d06e9306055254c91483c749ba4c1522e55324520e9d272930548b954c91482e749ea4c1522e55324520edd04c1c1548b954c91483a365a8705522e55324520d1f1689d1325b32149148343d5a8744c96cc8524520d1e5745a4325b321491483459dd7690c96cc8524520a17779cc9729b32149148245dde7365ca6cc8524520e3d132da348553614914838575a5605c7aed9524520fbc04c1815094369491483a730c45c18164da524520c9cd605d4b319369491483ed2170605425d1a524520a9d5784d970cb869491482a55de7365c32e1a524520e9d870930604b969491483a73130605c42e5a524520e8dc4c181720b969491482a755e1365c3215a524520a95779cd970c8569491482a6e4ec76581549a624520fb904c1815495369891483e64930548c954da624520fb285c1815097469891483ec6170605525d5a624520a93779cd970c8569891483a4e4c760542655a624520c93d35d8170d956989148322f4d8605c3655a624520c93d605d7b3195698914834734d4605b36959724520d1ad351816cda665c91483e54930548c954da724520fb604c12150d8469)
def oP8 : Packing:=(135,7,7,0,0,11,0,oP8F)
def oH8F (i : Nat) : Nat:=0x40194477900da06dd07db01fa02e204d906290696072d06a90575075c021003df0760058f00320343012c054b04260277029c05bf051c0530049d03ec02cc00a603cb01450707068b04730743009a07fe08090440067b073c05d903a9056e02d70269022f0811006c06e5016d0084071843d4028407a5010a004303bb020605ce060701be017801800077082205ad064c040243ea02500023055a00c801a90383482b065e077e07b50598015e030a4659023c04e204a3033b086b02a8037c06ff06c8041401e1475504b108540018031003f00437013e07804534063f04ff0506039904c8036800bc0849024907970489460505e8045b066b07ce083605f306be035c02f80110061d02bf00fa046a052100e00008005c07e40326474a01d101c003a063b000600197a1a0f4d5e00000d02000005011b4a182e050002003e00060d1800080b000200000100220203003c01232d0d010102020c12020100011f020400100100000801
def oH8 (h : Nat) : Option (Nat × Nat):=lookupWord 72 144 8 16 8 4 oH8F h
def oP9F (i : Nat) : Nat:=(if i<10 then (if i<5 then (if i<2 then (if i<1 then 0x269061bd718b16959624d20c3f8d03835db2c49a4186f5a6706bb65893483d9c2e090ae2d3126907b9844151549a624d20b33c6ca212ab4c49a41666cd94865569893483d8d2e0a92ead312690693d31e11655a624d20927e6bb82cab4c49a4124fdd7b3195698934828ddba44ad76d31269051af75095aeda624d20837eee12b5db4c49a4144fcd7656bb69893483db826090b433b92690497776acc64e7724d20f6a4982a4d2cee49a41a4f5a6305969dc9348289f9b6cab4d3b9269079d24c1526959724d20d2eac0b8648b4e49a41a575817149169c934824afdbae2922d392690693d605c6245a724d2090ff6eb9048b4e49a41ed61105455269c93482cb9ba648aa4d392690593b75891549a724d20b0f6ec122a934e49a410decdb7055269c934831bd22065aa4d3926906379844cb549a724d20b2b6e91232ab4e49a41655dd32465569c93482ca7ba848caad392690591f75891955a724d20b0beec1232ab4e49a4185f4cb8459569c934820bf9b6e0b2ad392690533b36d52999a724d20b672e89653334e49a416cadd42ca6669c93482d8dbaa594ccd392690513f36d95999a724d2092fa6e422cb34e49a41a5e4c15499669c934828bd9b6a932cd3926905979744b2659a724d20b2b6ea964cb34e49a41a574c19559669c9348349e982b2b2cd392690497d345c5659a724d2082fe6db8acb34e49a4125f5d1b319669c934828be9a2cb576d39269068f6681c32468824d20d16ed338648d1049a41a379a071491a209348344fb4ce2923441269068be681c62468824d20d0fcd038e48d1049a41a0fda671c91a2093483d7826090b43441269058f9748916868824d20b1daea122d0d1049a416375d5245a1a209348247f3a064b43441269048bf758c96868824d2091eeed598c9d1049a41eb4930549a5a2093482c6d9b2a934b441269068fc680c165a8824d20d17ad3182cb51049a4162ecd9549a6a2093482c1f9aecab4d4412690587e7409169e8824d20b0f6e9122d3d1049a4161ddd3245a7a2093482c37ba848b4f4412690585f7549169e8824d20b07eeb122d3d1049a4141fddb245a7a209348243fbb848b4f44126904a7b3715269e8824d20b4f2e8984d3d1049a4169add4309a7a2093482d2dbaa6134f4412690487f3719569e8824d20b0fa68b2cd3d1049a41a2f9a0718b9a209348343bb86d39734412690683f719a72e68824d20c3b665aa4d2b3049a41476cdb549a5660934820df9b8d8b4ccc1269051bb36d526999824d20a27e6bb6ad333049a4144fcd66c5a7660934820bf9b8dab4ecc12690517d345b669d9824d20c33e62b4cdbb3049a41a3d58170c916a09348346eb02e2922d41269068bd605c6245a824d20a3baea922d8b5049a4105fcd7725b56a093483ce9260a934b4c92690617932d21655a724520 else 0x6660914828dd9b6a934ccc12290789d606556999824520a27e6bb6ad333048a41e1d58168e7766091483c2eb02d2ceecc12290783d605a69dd9824520a2fc6da60d3b3048a4145bcd46cda7660914820bf9b8dab4ecc1229061d7315a36dd9824520c39e62b48dbb3048a41077cdc695b7660914830cf98ad336ecc1229070dd605a5aed9824520e17ac0b4d5db3048a4183f58172abb66091483d69260a92a6d4122907a6a5c1425d1a824520f4b4b82a4bab5048a41a1dcc78cd956a09148243f9aee1b2ad412290487f75ecc655a824520b0de6a3273bb5048a4121fcdc656776a0914824779a8e1b2ed412290507f35d95aeda824520a1fae89935db5048a4123ecdc549986a09148243f9aee2b30d41229048df355c7661a824520e1ba5c302d2d3248a41e76110709a5a6491483cea22119b4b4c9229069dc442cc6969924520f3b0882a4d2d3248a41c2f4b8605a6a6491483cbc26090b4f4c9229079714863369e9924520f2b290caad3d3248a41e3711069688a6491483c3ca42d3d114c9229041fd371816ea9924520eba45ca60a92a64c241a758c94c153694984820bf9aee4b66d29309060fd845caaed9826120c1f7113955db304c241837e5572abb6609848303fceee5576cc1309071f4681816cc9124d20e36ad3302d992249a41c771a0605b5244934838ceb4cc0b6a489269061de682cc6d49124d20c33ed3598da92249a41c6f1a0605b62449348307f34166370489269060bf69acc6e09124d20b7e16ea6090b4249a41cde1b75c121684934824eedbae2922d09269048fdb75c8245a124d20d3e4d038648aa449a41a6e9a0718915489348347d340e4122a9126907bd04c1516855224d20d7b0e02a2d0aa449a4163e5d8245a1548934824fd3a064b42a912690497b75cc96855224d20e7e098342d8aa449a41adc930728b7548934830fb400e5576c99269061f5845caaed9324d20c3e7113955db2649a41879dc472abb64c934834eb340e19232a926906997699c32465524d20d33cd038c48caa49a41a47da671c919549348346f340e41232a92690689f699c82465524d20f7a098242d0caa49a416765d2245a195493482ce6ba848b432a9269058dd760916865524d2093aeed598c9caa49a4105fdd772abb654934820bf9aee4b62d2926905bd2b7530549a524d20b7a4e9980a934a49a41ef413084552694934839e9260d8aa4d2926906bd24c1c1549a524d20f6a49818ea934a49a41af4930b3152694934839e9260a9576d29269051db36552aeda524d20f76098242d0ccc49a4126dddab319399893483dc9260a934b3312690599b748956966624d20b31eea12ad2ccc49a4187f1a032e11658934830deb4c65c22cb1269071f8680b15499624d20e3b8d01632ab2c49a41c675a62c655658934838de34058acacb1) else (if i<3 then 0xb472acee48a4185eda232d959dc914830bbb4665b2b3b922905b5cb75106967724520f6b088284d2cee48a41ed6110709a59dc91483daa22119b4b3b92290594f351936967724520f69888488d2cee48a41ad7110b31a59dc91483dac220a934b3b92290515f36d956967724520b25e6a326d34ee48a4144fcdb655a69dc914830f3988d1b66cb9229051cf351b36959724520a35e6a366d332e48a416de1d13093069c91483db41a898242d3922905b7876d30485a724520b6f16ea6090b4e48a41ade130b312169c91483db840090c66d3922907b70301218cda724520b6e36ea4319b4e48a41edc1304863369c914835bc18090c66d3922907b704c12150da724520f6c498284a1b4e48a41edc1304855369c91483da9260a92a6d3922906b787012120da724520c6f2e5a4241b4e48a412de5d17088369c914835b4a42e2106d3922906b59485c520da724520d67290b8c41b4e48a41a5e5217248369c914824b7ba966326d3922907b684c121911a724520b6d36ea432234e48a41ed85218ce4469c914824b79b8c9c88d3922907b5880121955a724520f6b0982432ab4e48a416d66dd4865569c91483da8a4319caad392290594f35193955a724520f69290c892ab4e48a41e5e2004859569c91482cbcdba90b2ad392290617b32d42655a724520f2e290c66cab4e48a4185dccb8cd9569c914824b79a8e1b2ad392290417f36dc3655a724520f2d290c88cab4e48a4185bccb9119569c914820bf9b6e232ad3922907179484cb655a724520d2f290d98cab4e48a41cde130486bb69c914839b8a4319d76d392290516f35193aeda724520e6d290c895db4e48a4123f5dab3191a2091483d743488828544122906c7931d216568824520b5b96ea20d2d1048a41eb6110889a5a2091483d6c220a134b44122907ad8441c26968824520f5a888466d2d1048a41633cd464da5a2091482c6dba464b4b441229058cf750c96968824520b13eeb192d2d1048a41ab7110b31a5a2091483d6c220a934b4412290585f35d956968824520b07e6bb2ad351048a41e9c52168e77a2091483d2e220d2cef44122907a788012169e8824520f4f098242d3d1048a4169e6dd485a7a2091483d38a4319b4f4412290586f3519369e8824520f4d290c88d3d1048a41e96521955a7a2091483c3ca42cab4f4412290487f3719569e8824520d4f290d98d3d1048a4107f5dab31b1660914828ef1b69834acc1229078dc801816959824520f1b898302d2b3048a416376dd605a566091483c6cb031134acc1229078d9605c26959824520a3b66db84d2b3048a41e355818cda56609148346eb036634acc1229078d9605526959824520a3b66daa4d2b3048a4185dcc768db5660914830af98ed2b6acc1229058bdb75816999824520f172c0c44d333048a41e2e581549a else (if i<4 then 0x5969d212e65524520e6f0d3b609090a48a418de5a7705b2214914839b8b4e90b664292290736969d216d08524520e672d3a42db10a48a41c5e5a7485b9214914831bcb8e90b74429229075712dd218cd9524520caf263a42d9b2a48a41e565a748655654914830bdb44e3d76ca92290417f75dcaaed9524520b7b0e89849834a48a41a375817258269491482dec5ba88364d2922905bd8744c06c9a524520f6b08818ed934a48a41af6110b31b269491482dea5ba88466d2922905bd4744c08cda524520f7a08844519b4a48a41ef411050a3369491483de8220d9466d2922907bc84414250da524520f78498284a1b4a48a412f71d070483694914835ec220e1106d2922906bcc441c420da524520d7388838c41b4a48a41ad711071c83694914834ee220e4906d29229063dc441cb20da524520d39c622e0c9b4a48a41a734c460593694914824e7ba966326d2922906bd8441c22cda524520e7b088364d9b4a48a41cf49306c9b369491483de4220a12e8d2922907b4a5c1425d1a524520f79088284da34a48a41af6110709b4694914839ec220d936ed292290735a5c1b26dda524520d7b0883845c34a48a41af511070cb8694914835e6220e2170d2922906b9c441c62e1a524520d6b88838e5c34a48a41a765c2604b9694914834ceb8cc0972d292290699771a332e5a524520d39c983885cb4a48a41a73581710b9694914834e3c66e2172d29229068dd605c82e5a524520a7b96ea215db4a48a41cf611088abb694914839ec220a1576d29229073d8440c2aeda524520a7b2e89855db4a48a41cf51108cebb694914828e79a8c9d76d29229051dd744c9aeda524520d7b0612215db4a48a41cf61106cabb694914839f436888284d2922905bd8b7510549a524520b7b0e8980a934a48a41ed611031d52694914835ec221662a4d2922907bd0441528cda524520d7b08838429b4a48a41cf49306c953694914839e9260a9366d2922907bc844142551a524520d7b088384aa34a48a41af60c244255694914839ad2e0d92ead2922904bdc741c1215a524520d7b08838442b4a48a41af511070c85694914835e6220e210ad2922906b9c441c6215a524520d6b88838e42b4a48a41a7711072485694914834ae98ec0b2ad292290695731e33655a524520939e6a386cab4a48a41257cd770d95694914824afbaf6632ad29229073d844152aeda524520a2be6bb2b5db4a48a41a2f5817258269891483dc9260a92a6d3122907b2a5c1425d1a624520f634b82a4bab4c48a41a4f4c7605956989148349d98ea132ad312290693731e33655a624520927e6bb86cab4c48a4124fdd7b3195698914824bebb5663233b922907b686911050a7724520f6e0e0242d1cee48a41adc521b31a39dc91483db826090b473b9229059673519368e7724520f6a290 else 0x482c7dba448b0ad41269058f774c91615a824d20b1deea122c2b5049a41637dd5245856a093482c5fbac48b0ad412690587f75c91615a824d20a1feed922c2b5049a4123fddc245856a0934820ff9b8d8b2ad412690497f35dc1655a824d2083fe6db82cab5049a4125fdd7b31956a09348247fbb16632ad41269041ff76ecc655a824d20a3fce8122dab5049a4147edd2245b56a0934828fbba648b6ad41269051ef750916d5a824d20a3beea922dab5049a4146fdd6245b56a0934828bfbae48b6ad41269050ff760916d5a824d2083feee122dab5049a4107fddc645b56a0934830fe96a60b2cd41269061fd2dcc1659a824d20c3fadb982cb35049a41a7e4c1549966a0934824fd9b8a932cd41269069bd30565659a824d20a37e6dacacb35049a4126fcdc595966a09348347e982c2b2cd412690789f59585659a824d2091fe6e30acb35049a4187f4c16d5966a0934820ff9b8dab2cd41269049fd345c5659a824d2092fe6bb8acb35049a4127f5d1b31966a0934828fd9b2a936cd412690517f35d956d9a824d2083fe6db82cbb5049a4107fcdb715976a0934824fe9a2e332ed41269051fb74891aeda824d20a3eee99235db5049a4147bdd4246bb6a0934828efbaa48d76d41269051bf75891aeda824d20a2feeb9235db5049a4143fdd8246bb6a0934828bf9aecad76d41269041ff37195aeda824d20a3fa68b2d5db5049a4107fcdc65abb6a0934834bf34ee010b4c9269061fe6e9c02169924d20d2eed3b8642d3249a4187ddba70c85a649348349fb4ee310b4c9269061bf6e9c62169924d20c2fedd38e42d3249a4125fdd772885a64934820ff9b76634b4c9269051bf36e5569a9924d20b37ce810ad353249a4166f5d1215a6a6493482cddba442b4d4c9269059b774c8569a9924d20b35eea10ad353249a4164fdd7215a6a64934824dfbb842b4d4c9269051bf36d8569a9924d20c37e65b8ad353249a4145fcdb615a7a64934830df996d35114c92690617f32da7a229924d2083fe6db8ad453249a4107fcdbb31a8a64934820ff9b92ab754c9269041ff371856ea9924d20b7b06da20a8aa449a416f62dd44151548934839ec220a8d76a91269073d22e5305495324d20b7a46e260a92a649a41af4930b315254c934820bfbaf66362ca92690417f75ecc6cd9524d20c2fae3c235db2a49a4185ddc78cebb65493483d6c220a8aa544126907ad24c15254e8824d2090feebd98cad1049a41e7493054953660934830ed996a92a6cc12690417f75ecc6d59824d20f3b0882a2a953249a41e7493054953a64934835bc220e516ea9122906979645ca2dd5224520e2f2d3a42dcaa448a41cfa1a4441b214c914838bcb4e90b7229922907dd04c191549532452093baed598c8caa48a41ef21a444142954914835acb4ee09652a9229079))) else (if i<7 then (if i<6 then 0x4e49a41a4fc857189169c9348343fcaae4122d392690687f355c8245a724d20d0feeab9048b4e49a41a1fedd7209169c93483cbcb0248aa4d392690597b76091549a724d20b2fa68b92b2b4e49a4145fcdb7256569c934824bf9b3662cad392690497f766cc595a724d20b2f6e9122c2b4e49a4165ddd32458569c93482cb7ba848b0ad392690595f75491615a724d20b27eeb122c2b4e49a4161fdd82458569c934824bfbb848b0ad392690497f77191615a724d2092fe6cd98c2b4e49a4125fcdc6059569c934824bf9b0e0b2ad392690497f762cc655a724d20a6f66daa4c334e49a416de5d12c98669c93482db5ba85930cd3926905b5b754b2619a724d20a2fe6db2ac334e49a4125fcd97158669c934834becaa60b2cd392690697d214c1659a724d20d2fa5a982cb34e49a41a5f5b53059669c934834bed1060b2cd392690697d2e0c1659a724d20d2fadc182cb34e49a41a5f6bb3059669c934824bf9aae0b2cd392690497f361c1659a724d20f27c882cacb34e49a41e4ed215959669c93483c9e982b2b2cd392690693f72165659a724d20b27e6c2cacb34e49a41a5f4c16159669c93483c8facac2b2cd392690497f37185659a724d2092feee30acb34e49a4125fcd87159669c934834ef340e2923441269069be681c62468824d20d2fcd038e48d1049a4167e5d2245a1a2093482cf6ba848b43441269059dd754916868824d20b1faec122d0d1049a41c6ecb9549a6a2093482c9f9aecab4d441269051bf36d9569a8824d20b2f6e9122d3d1049a4165ddd3245a7a2093482cb7ba848b4f4412690595f7549169e8824d20b27eeb122d3d1049a4161fdd8245a7a20934824bfbb848b4f4412690717b2e55269e8824d2096f66e2a4d3d1049a4145fcdb655a7a20934824bf9b8cab4f441269045ef750cb5459824d20a3fa6daa2d0b3049a4186fda632d65660934820ffbb465acacc1269041ff36dc16959824d20a37e6daa0d333049a4146fcdb545a6660934828bf9b6a8b4ecc12690517f36d6569d9824d20c37ee034d5db3049a4185fdc069ebb66093483dbc2e090ae2d41269073796dd215c5a824d20d3eac0b8648b5049a4187dcb570c916a0934834eeb02e2922d41269068df761c5245a824d20c3be6db8a48b5049a41877ddb714916a09348347eb02e2922d41269061df2d5c5245a824d2083fe6db8a48b5049a41a6f581718916a0934830df96ae3122d412690617f2d5c7245a824d20a3faea922d8b5049a416775d5245b16a093483dec220a8aa4d41269059fa74091549a824d20f1f2c0922a935049a4167cdd3245526a093482cddbac48aa4d412690597b75c91549a824d20b1f6ec122a935049a4147eddb245526a0934838fc922d8aa4d4126907b5a5c1525d5a824d20e6b6dbaa4bab5049a4163f9d0245856a093 else 0x7245a524d2083fe6c392d8b4a49a416779d02458569493482cedba448b0ad29269059d774c91615a524d20b39eea122c2b4a49a41667dd62458569493482cafbae48b0ad29269058df76091615a524d2093beee122c2b4a49a4147f9d0246bb694934828fdba448d76d29269051f774c91aeda524d20a3deea1235db4a49a41477dd5246bb694934828dfbac48d76d292690517f75c91aeda524d20a1feec1235db4a49a4107fddc246bb694934838deb4c58caacb1269079b9485a15959624d20e37ad3962b2b2c49a4196f4c82c565658934838deb9458acacb1269075b92c5525959624d20f276d3aa4b2b2c49a41c6f5a62c575658934838beb4e58aeacb1269071fc680b16159624d20e37ad3162c2b2c49a41e679a05958565893483ace962b2b0acb1269069be719106959624d20d376e3242d2b2c49a4187f4c72c5a5658934830feb8e58b4acb1269061fd320b16959624d20d37ae3162d2b2c49a41477cd56c5a5658934820ff9b8d8b4acb1269071bd2c5656959624d20e3ba58b0ad2b2c49a41a67dc6615a5658934828ef9b6c2b4acb1269071bd2c5c66959624d20a37e6db8cd2b2c49a4187f4b1b31a5658934830feb82d2d76cb126904bbe37150601a624d209776e9598c034c49a4126fdd9b318069893482dcd9aac02a4d31269059bb76580549a624d20f770882a2a934c49a416ecdd332152698934824df9b0e4aa4d31269059be36510955a624d20b3766ca432ab4c49a41ece97048575698934824dfbb8c8b0ad31269049bf366cc615a624d20937e6e300cab4c49a4126fcd870595698934824dfbb8c2b2ad31269049bf742cc655a624d20937eec598cab4c49a41a6ecc9549b5698934824df9b8cab6ad3126904bbb371526dda624d20937e6e32adbb4c49a41aef1c15c0b8698934835dd384b8170d3126906bb670d702e1a624d20d75ce22e05c34c49a41acf9c75c0b8698934834df392b8170d3126904bbe75dc02e1a624d20d73cb838a5c34c49a4166ecd9549b869893482c9f9aecab70d31269049bf371956e1a624d20d33ec2b8a5cb4c49a4126fcd8714b9698934824dfbb0e2972d31269049bfb75c52e5a624d20d37664aa4b2b4c49a41ed69705497569893482cdd9b2a930cd312690593f35d95619a624d20d6f2e3a42d0b0e49a410efdd632da561c934834deb4c60b2cc392690697d69cc16598724d20f67290ae2d330e49a41ec6d525d5a661c934828df9b6cab4cc39269061bf725a6aed8724d20a37e6c362d332e49a4146fcd86d5a665c934825bdba566300d392690497f766cc601a724d20d2ef2ab8648b4e49a41a5dc8570c9169c934834af9b0e2922d392690695f761c5245a724d20d2bf6eb8a48b4e49a41a5f5817149169c934824bf9b0e2922d392690497fb75c5245a724d20d27f2ab8c48b) else (if i<8 then 0x360e2922429269065dd6c5c52448524d20cbb6d938a4890a49a41973db471491214934834afb4ee2922429269065be6c1c62448524d20cb7ad8b8c4890a49a4196edb271891214934832d7b68e3122429269045fb749cb2448524d208bdeea3964890a49a4185fda772c91214934838df34cd83224292690717e69db06448524d20e7f0d8242d090a49a41cfa5b4485a1214934838fcb7290b42429269053f976d216848524d20e3f8d8122d090a49a41c7e5b2245a121493482cfcba448b42429269071ed6d0916848524d20b3daea122d090a49a416775d5245a121493482c7ebb048b42429269051fd76c916848524d20c3f6d9192d090a49a4187bdb4325a1214934824bfbae64b42429269073b6699106cc8524d20e6ecd3a20d990a49a41cecda6485b3214934839b9b4e90b66429269055f3748916cc8524d20abceea122d990a49a41575dd5245b321493482adbbac48b664292690717769c916cc8524d20aaeeeb922d990a49a4153ddd8245b3214934822fbbb848b66429269071b7699916cc8524d20e2eed3b22d990a49a41cfc521685b3214934838fa922d0b66429269051f7365a16cc8524d20e67cd3a20db10a49a41cceda7485b621493482addba448b6c429269055b774c916d88524d20ab5eea122db10a49a41567dd5245b62149348389fb4e48b6c4292690553f75c916d88524d20a97eec122db10a49a4116fddc245b62149348389fb4ec8b6c429269073b9485a16d88524d20e37a48b42db10a49a41ccf9a6441b72149348399db4c90b6e4292690557b748916dc8524d20aaeee9922db90a49a4155bdd4245b721493482aafbaa48b6e4292690553f758916dc8524d20a8feec122db90a49a4115fddc245b72149348389fb4cc8b6e42926907379485a16dc8524d20e2fa48b42db90a49a4145fcd9685b7214934831df38c883744292690637e71d106e88524d20c7f2e0a42dd10a49a418eedc6485ba214934831bdb8e90b74429269061fd704916e88524d20a3f6e9122dd10a49a4147ddd3245ba214934828f7ba848b74429269051df754916e88524d20a37eeb122dd10a49a4185fdc7245ba214934828bfbae48b74429269050ff760916e88524d2083feee122dd10a49a4186fdc6645ba214934830bfb8ec8b74429269069f6681c32458524d20d36ed338648b0a49a41a779a071491614934834cfb4ce2922c29269069be681c62458524d20d27ed338e48b0a49a4167e5d2245a161493482cf6ba848b42c29269059dd754916858524d20b1faec122d0b0a49a4147f5db245a1614934824ff3a064b42c292690497f75cc96858524d20c3fcd0196c0b2a49a4147f4db605a1654934834eeb8ac0922d29269069f5605c3245a524d20c3ee5c38648b4a49a41a6f58171891694934830df970e3122d292690617f2e1c else (if i<9 then 0x123fcdc64d876a091483d2daa4bab0ed41229048ff3719561da82452091feecd98c3b5048a4127bcd470d976a09148247f9b0e1b2ed41229041ff36dc365da82452091fe6c388cbb5048a4107fcdb711976a09148247f9b0e2b2ed41229041ff36dc565da824520d1f664aa54435048a4163ecd954a886a091482c3f9aecad10d41229048ff37195a21a824520a3f66caa55db5048a4145fcd7656bb6a0914820ff9b8cad76d41229071dd2cd816969924520e3ba5c302d2d3248a41c774b5605a5a64914838de96ac0b4d4c9229071bd2e18169a9924520c3be65b4b4453248a4186fccb69a88a64914830bf996d3d114c9229050ff36e886a2992452083fe6e510dd53248a41efa1a44414154898483dec260a8b42a9130907bd268d705495326120f7a498342a92a64c2413f4cdc5cd5254c98483db52e0d0a84ba130907b5a69d105497526120f6b4d3a60a92ea4c241ed6970685525d4984828fe9b698b42ca93090617f31da16cd9526120c3fae0b435db2a4c24107fddc686bb65498483df826090a62d2930907be844141509a526120f7c498284a1b4a4c2416778d94415369498483de926090aa6d29309059db3652154da52612083fe6e362c9b4a4c24127bcd470593694984820ff9b6e0b26d29309049ef752cc64da526120a3f66ca42d9b4a4c24147f8d9442bb694984828fd9b290d76d29309051ef35193aeda52612083fe6e3275db4a4c24107fcdc6c5a365c98483ce9aa4a9b46cb9309061ef311a16cd972612083fe6e346dab2e4c24107fcdb70da5a64984838eeb94c0b6a489269055de740c86d49124d20abb6e9190da92249a41575dd3321b524493482ae7ba86436a4892690559f758c86d49124d20aabeeb990da92249a41477dda321b5244934838ef340e436a4892690719f699c86d49124d20c3bee5390da92249a41c67da6b31b5244934838fe340c0b6a489269071bd699816d49124d20c37ed3598da92249a41a774d871491684934834eebb0e2922d09269069ddb75c5245a124d20d1fa6ab9048b4249a41a3f5d5720916849348347edbae4122d0926907bd8695105455224d20f6f0d3a20a8aa449a41e7e1a060491548934836f8b02e1922a9126906db9605c62455224d20b3f2ec122d0aa449a41a7e581325a1548934835e9b4ae1970a91269069b7699c32465524d20d33ed338a48caa49a41a57da77149195493482cfcba448b432a9269059ed750916865524d20b3baea922d0caa49a4163f5d8245a195493483dbc2e090b42ba9269073ba699b04848524d20e6f4d3b609090a49a4197e9c26c091214934832f7388d81224292690717e69db02448524d20cafce3b604890a49a4193f9c86c091214934832fb360e1922429269065f56c5c32448524d20cbe6d93864890a49a41979db470c91214934832ef else 0x24520f1bac0ae8d2b3048a41e37581721a5660914828ef9b6e434acc1229071dd2d5816959824520c3fa65b02d2b3048a41e3758154da5660914828ef9b6a9b4acc1229068fd605c3695982452083fe6db86d2b3048a41e37581615a5660914828ef9b6c2b4acc1229071dd695816d59824520cafa63b02dab3048a41c7d58168db566091483c5eae6c0b4ccc1229078bd5d5816999824520e37a5ab02d333048a41c6f4b7605a666091483cdcb02a934ccc1229078bd605536999824520a37e6daa6d333048a41e2f5815d1a666091483c5eb02c2b4ccc1229051bf36d856999824520e37ac0b6ad333048a41e3d58168d8766091483c6eb02d2b0ecc1229078bd605a661d9824520a2fe6daa6d3b3048a4145fcdb60da7660914832ee98ac0b6ecc1229071f5605a36dd9824520e3bac0b4adbb3048a41c6f581699b7660914838eeb02d2d76cc1229071bd605a6aed9824520c3fac0b955db3048a4123fcdb725526a091483c6d992a92a6d41229068fb3255254da824520b0fe6bb92a9b5048a4123fcd9b31536a09148247fbb3662a6d4122906aeb711425d5a824520d1ee61aa6cab5048a4123fcdc54d956a09148247f9b6e1b2ad41229048ff76ecc655a824520d1fc49b805ab5048a41a3dcd970cb56a09148347b926e196ad41229048ff365c32d5a824520d17e49b8c5ab5048a41a1fc9371cb56a09148347f1929836ad41229058fe365306d5a824520f5ac982a6dab5048a412b7cdc54db56a091482c779a8c9b6ad41229048ff371936d5a82452091fe6cb86dab5048a4123fcdc655b56a09148247f9b36636ad41229048ff36dc365da82452091fe6db88cbb5048a4123fcdb715976a091482c779a8c9b6ed41229048ff371936dda824520f4b6a92eadbb5048a4123fcdc655b76a09148347d992a9576d41229058fb36552aeda824520b0fe6bb2b5db5048a4123fcdc656bb6a091482cfd1b2982a4d41229048ff361c9549a82452083fe6db92a935048a41ef4930549536a091483db52e0a12e8d4122907b5a5c1525d5a824520e6b6dbaa4bab5048a41a3dcd970c856a09148247f9b2e190ad41229068fe32530615a824520b1fc6ca60c2b5048a41eb593054d856a09148256f9b8a9b0ad41229048ff365c3615a82452091feecb86c2b5048a4123fcd9b31856a09148247fbb36630ad412290687f31d83655a82452091fe6e306cab5048a4125fcd770d956a09148247f9b0e1b2ad41229041ff36dc3655a82452091fe6e30acab5048a4125fdd7b31956a09148247fbb16632ad41229041ff76ecc655a824520c3fc64a60dab5048a4147f8d94c1b56a0914839eb260a9b6ad41229043df371536d5a824520a3de6a326dab5048a4107fcdc64db56a0914820ff9b2e1b6ad41229041ff766cc6d5a824520b1de6a326c3b5048a4)))) else (if i<15 then (if i<12 then (if i<11 then 0x42d3922905b79355c4485a724520b6f26c38890b4e48a416de4d87152169c91482dbc9aae4242d3922906b79315218cda724520d6f26424319b4e48a41ede1b04854369c914835bcb9690a86d3922907b784c12154da724520d6f264242a9b4e48a41e5d9303255369c91483cadaa464aa6d392290593f758c954da724520b2de6a392a9b4e48a4145fcdb7255369c914835bca43662a6d392290497f366cc54da72452092feecd98a9b4e48a41ade5217148369c91483dbc26090b06d3922906b797012160da724520d6f262a42c1b4e48a41a5ecc95498369c91483db8a42a9b06d3922907b535495360da724520b2de6a392c1b4e48a41ade521b318369c914824bf9b366306d392290497f766cc60da724520f6b290aa6aa34e48a41ade52170d5469c91483dbc26090b08d3922907b664c143611a724520f6d290a86c234e48a41e9e52160d8469c914835bca42e1b08d3922907b6948554611a724520d6f290d98c234e48a4125fdd9b318469c91483dbc26090b0ad3922906b7930d21615a724520d6f2ee242c2b4e48a41ed593054d8569c91483daca42a9b0ad3922904b5f37153615a724520b2de6a326c2b4e48a4125fcdc64d8569c914835bca42e1b0ad392290497f365c3615a72452092feecb86c2b4e48a41ade5217118569c914828bf9b6e4b0ad3922906b79486cc615a72452092fe6cd98c2b4e48a4125fdd9b318569c91483cbca42c1b2ad392290617f32d83655a72452092fe6e306cab4e48a4125fcd870d9569c91483cbca42c232ad392290617f32d84655a72452092fe6e308cab4e48a4125fcd87119569c91483cbca426432ad392290497f762cc655a724520d6f264242cab4e48a41efc1a34c121a2091483df8346b824344122907b7869d704868824520e7e259b4690d1048a41b5e4c748595a20914830ff34065b2b441229061fb688cb6568824520c3bed2996cad1048a41c778b94c1a5a2091482ce79a8c9b4b441229051df36d936968824520b39eea192d2d1048a41c6ecb9549a6a2091482c9f9aecab4d441229051bf36d9569a8824520e2fc5ca60d3d1048a41ede130485a7a20914839bc96690b4f4412290717b2e55269e8824520b2de6a326d3d1048a4145fcdb64da7a2091483cbca42cab4f4412290517f36d9569e882452092fe6e32ad3d1048a41e765a560552660914832fc996c0aa4cc1229064fd604cb54d98245208bfae8996a9b3048a4187eda232d53660914822dfbac65aa6cc1229060ff6a0cb54d9824520c9fa65b02c2b3048a41e37573605a566091483c6eb8ec0b4acc1229079dc4c1816959824520f3b2e1302d2b3048a41c774b3605a5660914838ee96ec0b4acc1229071dd32d816959824520f1bac0b06d2b3048a41477cdb60da566091483c6eb02e1b4acc1229051df36dc369598 else 0x172552698914824df9b0e4aa4d3122906bb9605c214da624520d37ac0b9229b4c48a41aaf4c860553698914834de992c0aa6d3122907b996055254da624520d37664aa4a9b4c48a41e66d5232553698914828dfbb664aa6d312290593f35dc954da624520937e6cd98a9b4c48a4126fdd9b315369891483dd4b02a12a8d3122906bb9605c2551a624520f752c0a84ba34c48a41aee4c260655698914834de992c0caad3122907b3c5c1815d5a624520d756e2284bab4c48a41ee658154975698914834db9b2e190ad31229049bf365c3215a624520d37c64a60c2b4c48a41a6f4c96058569891483dcb260a9b0ad3122904b9f37153615a624520937e6cb86c2b4c48a4126fdd970d8569891482c9f9aee4b0ad31229049bf366cc615a624520937eecd98c2b4c48a41e6f17060595698914834de986c0b2ad31229069bd32181655a624520d37a6e302cab4c48a41e6e58150995698914834db986a9b2ad31229049bf37153655a624520d27e63b06cab4c48a4126fcdc60d95698914834deb02e1b2ad31229049bf361c3655a624520937e6e30acab4c48a41e4f58131d9569891482cdeba26432ad31229069bd606cc655a624520937eec598cab4c48a41efc1a34c12161c91483dbc34e98242c39229065f932d2164d8724520f7e0e0242d1b0e48a41edc52171da361c914839f8a42e5b46c3922906b7971d2168d8724520f6e290ae6d1b0e48a41cfc52168db361c914839f8b4690b68c3922905b5b769525d58724520f6e290b46bab0e48a41ed4d5268d7561c91483d78a42d1b0ac39229065f9484cb6558724520c3f6d1196cab0e48a4187dda332d9561c914830f7b4865b2ac39229059cf351936958724520a3be6db26d2b0e48a41477cdb655a561c914839f8a42d1b6ac39229059af351936998724520a37e6db26d330e48a41ec6d525d5a661c914828df9b6cab4cc39229065f972521aed8724520e7e290b475db0e48a41877dc9696bb61c914830dfb92d3576c39229079f16055268d9724520f2eac0b8ed1b2e48a41e5d5815cda365c914838fab46c0b66cb9229065ed311816cd9724520f3b898302d2b2e48a41e76581709a565c91483caeb02b9b4acb9229071dd605b36959724520a3be6c366d2b2e48a41e55d7370da565c914838eeb02da34acb9229051df361b46959724520f3b2c0aa4d2b2e48a41c775a5605b565c914838fab02d1b6acb9229061f7321a36d59724520f37898302d332e48a41e6e581549a665c91483c9eb02b9b4ccb9229071bd605b36999724520a37e6c366d332e48a41c6f5816d1a665c914828df9b0da34ccb9229071bd605b56999724520a37e6c36ad332e48a41ede1b34c12169c91483dbc36898242d3922907b786d530485a724520f6f05c26090b4e48a41ede1b84c12169c91483dbc576982) else (if i<13 then 0x7b098302d934a48a41ef6170605b2694914835ee180c0c66d29229069dd325818cda524520d6bce3ae0a1b4a48a41ef51306054369491483de4b02a1286d2922907b5c5c1815cda524520d7b8e0302b9b4a48a41a774c96058369491482ceeba264b06d29229059cf351c960da52452093be6cd98c1b4a48a41277dd9b318369491483cee2e0c0b26d29229069dd31d8164da524520d3ba64302c9b4a48a41a774cb60593694914834ee9b8c0b26d29229079d96054264da524520f39ac0988c9b4a48a41a77581b3193694914835ee380c0966d2922906bd9605c22cda524520d6bce3ae0d9b4a48a41ef5130605b36949148356e990c0b66d29229069dd325816cda524520f6acb82e6d9b4a48a412f5cdc60db369491483ceb26064b66d292290599f758c96cda524520f6b8b8302ba34a48a41ef25815097469491483de4b02a1368d2922907b5c5c1816dda524520d796e2284dbb4a48a41a75cd970cb8694914824ef9b2e1970d29229069de325306e1a524520d3ba64b02dc34a48a41673cd464db8694914824ef9b8c9b70d29229073d64c1b36e1a52452087be6e366dc34a48a41277cd970db869491483cee260c0972d29229069db709832e5a524520d33ee33065cb4a48a41a7758170cb9694914834ebb06e1972d29229069cf60dc42e5a524520d3bc983905cb4a48a41a77581720b96949148346fb06e4172d29229049df74dc82e5a52452093bf6eb905cb4a48a41cfd1b34c18169491482cee9aae4b02d29229051fd36dc9605a524520f7b098302a934a48a41ef617060552694914834eeb02e4aa4d29229049df361c9549a524520d1fae4b02c134a48a41af71c060453694914835ecb02e10a6d29229069dd605c914da524520f7a898302a9b4a48a41ab74c860553694914834ee992c0aa6d29229079d64c0c954da524520b33eeb192a9b4a48a41277dd9b3153694914825eb9b8a9b06d29229069ed3118164da524520d3ba62b02c9b4a48a41a775c560593694914830fe996c0b26d29229061fd325816cda524520a37eeb192d9b4a48a4107fdd9b31b369491483de4b02a12a8d2922907b5c5c1815d5a524520d796e2284bab4a48a41a75cd970c85694914824ef9b2e190ad29229073d66cd30615a524520d3bc64a60c2b4a48a41a774c96058569491482ce79a8c9b0ad29229049df37193615a52452087be6e366c2b4a48a41277cd970d85694914824efbb36630ad29229079dc5c181655a524520d3ba61b02cab4a48a41a774c760595694914834ee9b8c0b2ad292290695f31d83655a52452093be6e306cab4a48a4166f4d57258169891483ddc2e0c0a84d3122907bb84c181549a624520f770b8302a934c48a41e6e5d96055269891483d9cb0263aa4d3122905bb9744c8549a624520f372c0992a934c48a41a6f58 else (if i<14 then 0x69041ff36dc154d9824d2083feec598dab3049a4107fcdbb3153a64934820ffbb7662a74c9269041ff36dc36169924d2083feedb86c2d3249a4107fcdbb3185a6493482afc9b6e4b02a9122907b59695812dd5224520d6f2c0b945baa448a41af65a5704b8548914835f8b82d1970a91229079d9695812e55224520e7e2d1a42dc0a648a41cde5a7485b814c91483df834698242a9922907bf068d704855324520afe26db0690aa648a41edd1a74c12154c91483de9374982a4a9922907fd04c1815495324520d1fad43825caa648a41f74930548b954c91483ced340a9172a9922906dd9705522e55324520e3b6dd2a45caa648a41a76dca548b954c91482cedbb4a9172a9922906d7931d216e55324520a37eeb172dd2a648a41cfc5a3486bb54c914832fc99290d76a99229041ff365caaed5324520e7e2d1b6690aa848a41ef85a361121550914839ecb4ac0b64aa122907bd168d2154d5424520fed0b8302a12e848a41ef85a3485545d0914839f8966d1a432a922907b785c1a34857524520feb0b8302a92ea48a41cfc5a3485b35d4914839f8b4690b68ba9229073f86c1a34848524520e3f2dcb469090a48a418fe5cb68d21214914839fa360d1a42429229073f16c9a34848524520e3eadcb469090a48a418fd5cb68d2121491482afaba264b66429229071f3688c96cc8524520e3ced2192d990a48a41c5dda7325b321491482abbbae64b66429229073f1485ca6cc8524520c3ee64b94d990a48a4147dcd9729b3214914839f8b4690b664292290737969d216cc8524520e7d2d1a42da10a48a41cf95a3485b4214914839dcb4690b6c429229073b568d216d88524520e6f2d1a42db90a48a41cdd5a3485b7214914831fcb8690b74429229063f570d216e88524520f7e0d1ae090b0a48a41efc13068d21614914839f8966d1a42c29229073f168db44858524520e7e2d934690b0a48a41c7d5b968d2161491483de9344982a6c2922905bd67693054d8524520ffa098242a9b0a48a41ef45a348553614914833ec99690aa6c29229073f168d216cd8524520e7e2d1a435db0a48a41d5e4b76112165491483abc96ec0a84ca92290797969d2154d9524520eaf25ba42c1b2a48a4187eda232d83654914832be98ec0b66ca9229064fd321816cd9524520f2f2d3a42c2b2a48a41e575a5604b7654914834eeb4ae0970ca9229069f5705a32e19524520e3bad2b035db2a48a4195f58171ebb654914830ff340e4576ca9229061fb689c8aed9524520c3eed1b915db2a48a4187bda4722bb654914830efb4ae4576ca9229061fd605caaed9524520f7986a260c0b4a48a41e770d94c18169491482cee9a6e4b02d29229059dd36dc9605a524520d3bac0b929934a48a41ef61306054269491483dec2e0c0a84d2922906bd972d81509a524520f else 0x2c1e5828b0296002bf657a4aeb95c52b4c5650ac115702ad65598ab0955c2a945514a99952e2a525490a8f951a2a2a5440a8595062a025354a5b14b12958529ca4a949029165218a40947c28ee51c8a30144e287850a8a0c141328024f889e19397270a4dcc9b0934f267a4cac9931321261e4c2897c12e625c24b3c95e92b825664ab8954929725244a34944127624c84948920122e2438485c8fc11e623a847088de91ab234c46508c1117022bc4530896911b221243dc87290d3218242bc84e908b210c4204837906a20b0414c827103c206e409480990011fde3f747e58fb91f4e3e547c18f641ea43d0079d8f291e483c7c78d0f081e063bf877c8ef41dde3b747658eb91d4e3a8874e8e8b1cf239d07378e6a1cb0394c7270e3c1c6e38c87100e0e1c1238106f90de01b8236bc6ce8d7e1ad835686a40d361a4834486800cee19b832f46558c99190e31d46318c51187e30b460d8c0917ee2f945e98bc1175e2ea85c58b6c16b42d2059b0b31163e2c345840af615e22b7c56d0ac8156c2ac45560aa715442a4053f0a7914e829bc5350a6514a629385248a44147e28e851a8a23142227fc4f689db139226dc4d28993131c25f04b50958128c24d0491091d121623e447388d511a0232c46308c1117822dc4528893110221bc42e884b108c20d041108101016201840087fc0fee1fc83f687e80fc61f783ec87d40f9e1f283e287c00f761ea43cb87850ee61d843a7873d0e701ccc390870f0dfa1bac36c86c70d841af435586990d0e19d4338066b0ccc1950321063d0c56186430385e80bac16dc2d285860ae8158829b05240a24140027704dc099412e025984a1091e11f42358459088e106c1f783b606fa0dac1a6033a066a0cc018f030c05f40ba016b02c405640a8014d828904ee09941298241047808dc1190220041c07f00f501d8038c06d00d1019002fc05b00ad0148026c0490089010001dc037006b80c5016602b8054809701240234044007600c80148020002e0038005c0090000f7b144220a8aa449a41ef60b84415154893483dec260a8b02a9126904bbb75acc6055224d20f7a544260a92a649a41ef48984c15254c93483de9170982a4a9926907bd2321305495324d20f7a498302a92a649a41ef4930548b954c934835cdaa4e3172a99269051bf758b96e55324d20f7e09824298b0a49a41ef493048553614934820ff9b8c8b66c29269041ff771916cd8524d2083fe6e3235db0a49a4126fdd6b3181654934820ffbaf66362ca9269041ff762cc6c59524d2083fe6e362c1b2a49a4107fcdb70583654934820ff9b766306ca9269041ff371816cd9524d2083feec598d9b2a49a4187f5c1606bb654934830bfb8ec0d76ca9269041ff77181aed9524d20c2fee3b075db2a49a4107fddc60ebb654934820ff9b2e4576ca92))) else (if i<17 then (if i<16 then 0x1855b0996128c23d84530856100c1ed83b307160d8c19d82ab0506096c119820b0226020bfc57efafc05f42be097beaf785eccbd857ae2f575ea4bd357a42f435e62bcb1793af225e20bbf977caee75dc4bb7576c2ed35d9cbb257622ebf5d74baa1751ae915cfeb9b572dae495c6eb8957032df45bc4b7416d8ad9f5b1ab5ed6b4ad4a5a70b49968a2d0259e0b3796662cba596ab28d648ac7f58f4b1a162b2c445864b0b560dac0957eeaf955e9abc1575eae755c5ab7956cead21594ab17560aabcd56a2acf5594ab155602aa1551ea9f5535aa4c5474a86d504a9f753caa7194e0a9bc536ea6954c9a98152c4a541498a9125200a3b9474a8e451bea301457289c5114a1e143328545084a08d408a7f24fa69f053d7a79d4efc9de53ba276f4ed49d613a327414e789cdd399272d4e509c8d38f27194e289c3d38527054de69b85367a6bd4d709a9934a26824ce09979326263a4c50988d30f26194c28983d30526054c0097ed2f4a5d74b8a96cd2d7259c4b1496152b9a5614a9e94f528f250c49f493a126b24c4496492b52542496490891c9236a46848c69145226243a4850905920223f247da8f6d1eb23d147988f1d1daa3a3473c8e651c3a38246fa8de11b9a36e46b88d2919c232646288c0917822de45988b1d16122bd45568a6514a228f45148a15139a261449e892911c22264428883d0fea1f843e687b90ee21ca437086990d0a19c432e86490c0217b42d2855d0a2a133425c84a50852105420083ed07b20f141d8839d07120d0419682e505a20a24120822d043208140f881a902c2046408280f10152018400c7fd0ff11fdd3f967ee4fda1faf3f207df8fb61f5a3e907cd8f921f1f3e1a7c20f7b1ee43dbe7b68f6a9ec33d7c7ae4f5a1eaf3d547a60f499e813cde79a8f329e533c9c7924f221e323c407838efe1ddd3bb07718ed39d953b0675c4eb61d5a3aaa750ce989d1f3a1a7420e819cf139be7334e5d9ca93948727ce4d1c953920722ce431c8138f871dce391c6d38d07158e221c3238407038dfe1bea37b06f18de09bbc376e6ec8dd01b9b372c6e44dc61b8736ea6dc0db59b5936a86d08d981b2b36326c50d879b0a35f06bccd709adc35ae6b14d601abb356c6ac4d561aa735446a74d4c1a93351c6a24d3b9a7234da69a0d319a5e349868e8d1a9a3034566864d0a1a0f34146814cf999e133b8675cce919cd3390670ccdf19b9336866bccd519a53340666ccc4998432fe65b4cad9949328864c8c969928322c6410c7918e0319c62bcc4e9898310c61d0c37986a30b0614cc20983c306e60c8c10180e2ff85fa8bec17c62f685e88bc8177e2ed85d68baa97432e7c5c7cb8d17152e205c2cb8317012df85bdcb7916ed2db65b58b6896cc2d8e5b08b5e96b82d4c5a50b41167d2cf05964b2a16352c6058acb131614 else 0x897ad2f125d94ba097372e5a5c8cb7f96c12d3a59e4b2a96172bb256d4ac8956d2ac654fca9a95112a0e538ca6c94cf298a5284a3e9459286a50aca109417281a4fa49ef93d527624e349b4934526764c5c97992cf258a4a8493e9259246a48ac9109217241a480c8ef91a122c644fc89a9111220e438c85f908120ba40e480a8ff11f9a3f0c7cf8f7b1eae3d347a18f1f1e2a3bc47668ec31d723a547388e671cba387c6f08dbd1afe356c69b8d131a12339466d8cb7192631bc6258c2717d22f145dd8b97171a2e0c5bc8b6f16ca2d6c5a88b47167a2c645878b0515f62b5c5668ac3153e2a545388a33145228144f089bd12fe250449b891311de232c453888310f221bc432885b106e204c3f787e50fb61edc3d687890e961c9c38e87130dde1b2c36086b70d5a1a8c33f86750ca218b431186190bea16dc2c9856f0a96143427484ab08da112420583e707860e7c1bd837106ce0d741a98349067e0c6c17b82b9052a09c4126822903d606b40c4817f02b605440a3813d0232043c07580e1017a026403a8051005a008c00c800f0009ff83fde7fb2ff1dfdabfa37f3cfe65fca3f8f7f14fdadfacbf477e6afcc1f95bf267e28fc3df7ebeeb7db2fb1df5abeb07d56fa65f4a3e8f7d14fa15f39be617cb8f95df293e407c5cf871f053df87bccf751ee13dbd7b56f631ec3bd757ac6f579eacbd477a6af459e7bbce579a6f305e57bc9d7916f1e5e33bc557886f0f9e163c1a7810efd9df23bd2779aeeeddd4bba47724ee35dc43b8376fcede5dba3b6f76d4ed61da9bb41765eeca9d8c3b13761cec25d7bbaf275c0eb05d5e3ab7754aea4dd473a6f74d4e995d303a4e7478e8ddd193a207436e859d08ba0c73f4e7a1cf1b9de7398e71dce139b07356e699cd0b98f7314e615cb9b96e72b8e55dca9394d7276e4a5c92391f7234e455c81b8fe71d8e39dc6ab8d07196e319c5a38af7154e295c50389b7112e1ddc32b8467068e089c0837fe6fd8df69be437c36f62de7dbc6b77b6eecdd91ba2b7266e42dc71b8536f86dccdb51b5ab6966ceed9c9b30364e6c78d8ddb12b6136c02d7bdaeeb5be6b3ed669acab5836ae2d57daa6b53b6a38d45da82b50069f6d3a5a7234d26980d2eda54b4976924d235a44347668e2d1b1a33b46268a0d0f9a16341a6810cfd99f8b3ec67cecf899eeb3d867a6cf399de33b76764ceb59d433a3673cce319c3b38266facde19b9b36e66b8cd299a2b3406676cca598bb3126600cbed97b32f165becb3596432b66562cab1953b2956520ca2d93cb27464dec9a9932b26064b6c959928b24c6474c8d5918321e6432c851907b1fd63f0c7998f0b1cf6394c7158e031bb636cc6c58d631a7632ac6418bf316c62cec5898aeb15862a6c53989e3137624ac44d88731096208c3fd87d30f561c6c34586630c76184c2c) else (if i<18 then 0xa82000190200008595210011c200001841020302006ed82000000000000000782080000031c4101e84000003c2000002a90804c200000000000000000004c20058002e000802020700040042485092170005c001124840cc028100c42070005c0010000b2100164200000b2102c840b2102c840b2102c840b2102c8409216e28538a102c84004908190403f1000000000000032308000000005cc057301002840001701c84000f0c8c400000da10000002c0020770a0e4201e01a0807a1e410407a1000006410407980800000000000002e01600a060160348800000b0200000000178a15e28473011e2840d6101f142c8201f8805c028100d003c025181482bc50af142bc508f143c82080128208250413cc040e00080c02000007980800001804f3010180533012cc04b3010005c0682024871041c41040f00082904158004068119184068100b00d040520812420520814820520814820520802c348208000170829041000f30100128244b0a7142c820a7142398087142c820a71421c5080c044c264106904101e602000178a10000001e6027000ea08207708007c509f14200025041000f30100150411e284002c705e00195c00d052820aa08205201f8805a154105504101f8435214e28538a194105504102900fc45a90aa0825c509a08268209a08258e0966021c50a6a429a9086a429a909a08268208005c02810c8c06820290578a11e2840798080c0203e28403a9080752103b04000000ea194104000000008080000000e06081dc2e06081dc2e060a0e42e060b818207708009218c10630416030580c16030400560814820060816420000000381822390b81822390b8182239080e001110847041000000000000000000000381820390a8182e06090dc2e06080dc2000034204d09c182700081482bc5080070009084203e09f142000046e101804003d080f4338208ee007a29c10402c03d10148204a029080a410250605e0160268d018138004f04121084f0413c10538a10723825480908c254809714200d0d16776c0521eed885e0521eedb91c4590061376dc8e22c80308b820d16502a21c104003c105c0c103b85c0c103b85c0c1703040ee101c00222108e082206081d420001c0c103a84e0013e284e0c138004f04111084f0413c1040c411248751c11a40444611a40478a13c105c0c10082021a908005a9080002c105352101e8407a101e8401a100138a1a05540627fccfe79fab3f427df4fac9f1b3e227c1cf649ebf3d6a7aacf439e7d3cb2793cf229e3b3c62789cf0e9e133bde772ced39d9d3b267624e989d273a06737ce6a9cb1391a71a4e229c0737c66efcdcd9b91370e6df4dac9b3536226bb4d649aa5353669dcd369a49344a6804cfb99ed33c66764ce799ab32da6524c9298e73186627cc3d985730665fd4be else (if i<19 then 0x42610001420590808b210000008080068101a6c684004e803b9808006931a100005c70440e100071c10000000286e341000010100138a100009c508000300817be1000058e0af14200000798083504101f1420001b1c10000000f14206d0a6a4202e00b0801a1700040721037850101029040ae1001b42d8e0b714202d08001010170058402e00b08000040535214d48405c10170058402e00b0805c01610001010358538a10014820570b6a42dc50aae0202e00b0805c01610000080aae03bc50ef143bc5080b802c2026a42001ae02035c04d701001bc20080800019184000000de1037840de1004040de10378400000000000101000000000601000000000ec100b0400001bc2008080e0c1000000508020205e28400001d820001902000000000003cc04000180400001d82003b0400760800000000001d8206d4840ea10000000001a10019821590800000000030800c20000e0c101c00200000000000021282000001f70028802c10fb80b84623086e405c20fb80b841f70170800015040000000001bc200010b216030403b808000000000000de1003dc205908c002a21091642159081bc21f70028801a100b0484610fb8014400d080582c230916421f50028801a100b05846100984042122c841ee122c8408230804c200d08002c138005046111084006f08e0820160a08c2059083dc2859083dc205909c002221087dc05c20fa80b8485908564206f087dc0282000000fb80504859081642700086e405c23108437202e121642159081bc21b70170800003dc20f709c0021f701708c4210fb80b841f5017080de10a48400007dc05c205c8509210068417210248401a1380043ee02e1088421f7017083ea02e1011c2159081bc21f70170800001c0c103b84000000000000000007608ee02075081d82038304e0012040484212040481010320405410000000000010dc240c0a9642bdf080056112c8400470b81820750b81821f5adb08072101c8558a1023851e8101b840040605018103a8400076d8201d4840261031047521009840358080000003420080800013080000003ba1026840a414db0404611a48536c11a48407a100010080818820000070009f1420490800ea1023844181000c0200000261031058b2162c84000000c41031642c590b1642c59080104a3dc080000000000f0410019020006840101000002a40484612a4040062c858b214250408e15fa0400470811c20000f5018240605018103784fbe1ddb0576c10004c2070305c0c1000020c08000000f04101e0827820800008080000108402c107a841ea100b0034400068402c00d1496420650819420024840ca908e083008080b420012a4206208ee02ca9081642000000000000000038304e001204048421204048101204040c8103204000000c810000 else 0x10b0100b00345e000bb7c2076f850b0103300fc4007b17d3020000001083d8a10000000000030a124200308000017005801a3000042008080010100084b5210368609403f101b4200d081b4200022b212d4850b2100a0407e1037840606080058101605c00100000074682034a8d080da1ecc06d7081e100d0258e0a52436b80c5242034d8d0800a1009840261d830500e10000e000a3dc05c242c842b2100a061ee014143dc0282017040b2101704002e08005c10005020000b1c1b8d0500e1403840000131c1001b8a16e2840b216e28409c5081d820590800d61018040d6175c040000006b80907800a220f0014478e082e34106e60206d081b402c2036856001404046921014040b480ed2028080800008081f8a15e2840003b06f30100171c00514e3801621a4840da02e10f7c2808081482001604081e0c078331a081b423230c3dc05c20040408080800000000002010100010080800066080b521036805840035840ec10170571c00514e380162000b823df0a020202c090e420000006b0a6a42808080131a080646187b80b84008080080809e60200000fc508178a103b04003d48503c041100fc34b80d2e0304a01f8801a182500fc5b4865c080ea19c700fc4cb808f7c2808080fc20000000010428410b2e203c2583050101a5c04646102932e050f5017080101020202000000a1000202022f0571c103a840ec12208400001970103a840cb8080c02cb8080000000a404a12128204908148200033aa10771420300b800207b080c020000c020000003008014200020941825060941031853301ea40609418250400760a12802c2001d8304a08000760c178304a55c0a094ab812ae020750aae020750aae020750a12428490a124204a081092102c84fbe13ef840b2102c84044908124205ef84)))))
def oP9 : Packing:=(1560,6,7,0,0,15,0,oP9F)
def oH9F (i : Nat) : Nat:=(if i<2 then (if i<1 then 0xca0b2c80d3b860ec0c08e08bf528f383b0002be8075e41ab7007464332e10dd402528587b0b15a0759c2ed7846f6071d604a282149847d90091c09c602a5683d1941658014a80274033534782c0f5dc10f583c680625490f84200020a1602e44116e407aa015c608d541600c0acc00af304db00b1250e47028fe374fe15d000f8c03e074a29405d8c033b01f820b41a16a142db784b0f0581c0764400b300be60874609a691c09028bc061d80465018a282b0d036ba115700f31824f50b0dc003a02e14852a306068130f00894802a6070a80dd082283c1324408f18001b400b1da2d02637c008010020bc0400001e01c0e82bb720302d000036009a1b25028208001a2704002cc0af662000828317ca02dc703800a3661280000e74c7201e01f714119c60bc0980e81723e32408018032905a1812918054561f5000000050520001280182005a35c5a0183f402c3f8000cc0082082a0180100019100056c0180301409802852040268018000002c43702e024000060090022c003a23000004000ee04c000108020a01081f91f12800d1282100c6b80180600a1d0048380a23d00a2171c6150018040ca000008005081e81b0d7064000048040562b07e89301e10c000a8012048478260b20180c00601c000020000020942600804a0480080f00400002022014008000001f22302401823a1280b03001e1b00e80004c034258870340283103100049c0b80303e4a401002166034858050000381d0190ac0c4100070040100f0000200e4008000fa13c180040262bc0082c06a6100004b000004190010060444300300e0205000d01a02c0300708a00c17800006280200000021e42400413a000230570680200f01f0040e401800002004008020a0248100c705c0041d00102c0000500e00208802003084004010a206272802000270010210000620082d805082005088000206900680503a00cfc07400e03c010510000c4000150080880000601e008008250fa0b802000002024348000b40081101b00a09013000006004a38000001a8128360040482a00301e0000101c172104670090100042702202e03c000010060000680100600819005012038028140020280500000254800127000030000080020a4008110701ac000000200080608100a004230000000009180105618c00007002018000000ac0047c001006044140000180000781900003c1080500a0f81a80304202c228010c404c000020080a400007000010180040100144700212c00000007014014038140202f4138020000840984d02a01c1280200206c0004a09a0500302300028c0b81e00a0082386f0000040000200803c008230040000080a000004368010280040887700e00000801030024028000440001180001005c00003006008010020aa034118150000040000100000804006 else 0x9180a2385cbd01df40bb140857814920a16e08cb51ed60380a010bc13bfc086a029dc4335a134d8052f81b7a012f008b3c19a180366088b61638c1d4781cb5015b6140801aee0552a041c2176dc15ab0152c055540d91d2a3f8275b09fd60ee7817cf837830a4d209c80022a8564c41ad41465012c98550901f781403dce150496909ffa0a7ac06990344603bfe90cdc2407006990158a13ae81ddf039f70ad56165d426ec014d105e6008aec1c62a0db10497284b0d214284b7002c129168c104281c9503536093a41108250c70422407d20219504fc601f920e5f813b303f540720415c6c0161857850ac04120c012ac01ff60698a160492111042140477c924190b6184a75073661765007cb0579b64366182641c0a054f50154a06f40162b836de0340c826a40cae82d1904604181b401f18404e018ba0140427242578746200167b0247c849ab03edc016400cb6853310b9ec16e08120302a0e0578614e58101904c07016ba8360c1407056d4084601290d1d4d00c7607538124ec308b02a9b022040ad802373817e60aabc0d6000aaf8028e0152c110e420ea81b990770a0d9bc14c2007a603376948c800380514d0b2880f72819c800ae200f306f7c014970249606424109c81a36802ef423ac15658011582b840989a0185421c484db3033880bd102f9405fdf00b6e12458092c83888424f411b052c0ea0e713c2b802ed41789809210bedc024300636840a904fa405090155e29c23001b6031341916a37e50223a10fa0085a840b803dd80ecc4070620d4c07ba607088158b0382a00fcc00fe803e6a3b9e005b405ef8136401d570ae600af882b77045cb0756a0ff4d27f2802440348a0613426e4033a2082260ec981810829b3019f20e80c303d04b240a48a11a582177824c0080e2076e401d3053ff06a0610060131d840cd0778410835056a838a90c20204b8c05398262b095b60af6c175b8494d0317014c1c2c6505f0c05648060cc1e24035b30af700a315099701dc009e4e180fc18d985113420600cce80419827fe06f480ec602bfa845344ad6e143d021130505304a0008a181f6b814120beac1707c2467212414a0ba8eb701432855f40238817f1c2f37845f04b08a0d8441668814bb039aa105ac21ff85b4909ae0005c02dca85a180681e007452a7fa42180b6a8096e909890345002404168f005b104a020166c8fe601242842b005c6e048ad0912035150064e0454c02e0807b409734138000df2021760bc4806e001fb684d410848a06eb105a80282d4aefa0a20c022082bb208e8a07d782455a25cd00726910c42f19036ad0b3b015eb42187058fb085900fb34142281a8d08a44000c8255b04c6b0872603cc82cb501e190910202e3c04cc85d1802308074c9098681ec70378e0a6a91eec021b302946982d40f43003c2086) else (if i<3 then 0x6fe82e440a90a053040c3a04d10241500da2c0804a431b4a94c005350a3801f7501b7e17b748e2a012a5057440c7581f0c037b34068a0ef8419da820020b4c60cc492c2981e7201d60003182f4981bf0036660faf42df905cc5425c604f84250c05cea09ad20ff981d24012100010204324164a80a67076a402d242a13859b6082080e9d407430139204186113d0098a8434f08894032cd303380dd206dc80fa8c04e92464e09bde0ba2c16f305aa241d02158b425b583a10426b40e3441f4802429026e8178340b088170c0bfc40fdf00d66851d20a4060e45c0af70433a042b013db41e6982a6403bc00c674230c8043e063ee0e2541923022e001fe6064941dfe84b8b039e084da80b1284a254a6040c128260b84e280a8120797c066b822d107f8c0272c09d5801c7419988e919287e002fe484e40bca4290c01b1904adc021141b650558e05ba616e802c12a382c05132177d80aa7021c406c18009f904ceb3220091c20e8e428920166102d7c0398d07f882c6203c740c3e02408850950932a183e509fda3abb04cee000a01b18846b8004c8146d402790164149c48138fc30aa0133f0939e83dbc2519a030002af883d240d14823c102a700326c1b3a8283b0811803d980c6785e4909cf005160275782233018060996802170365d07f4601bb8082d2516e020800afe02d6c827ad03c100ebf42069a198709e1a11e78220280a2506f9413d1c0ec4852b60b53e1209817e105efa073ba171ec2c4905379051500ba6409b0a548e0356004c9c2eba860d40690203480305f0463c02e3a06ec423f702a300025606c1c0e8b015d4061301295807a500f030bce6868182b5c00468016f80169d087d811a309dc40c5b006858013a0a8a40d26827cb81aa305eb8119000464839650b87c165681e85801bf0ab4c01a101302047c70473a16ee8107900a850716895da41569855164136e16b241e9083b74062be0add420758124b058f0106dc297b853d947dce07be02e6c001e9033d614b24257985917425040935809f8056570b7dc037281b4f8495408e54914ac195400e4108b3214b4c0bbc84fd80331e0716c025f844a1026a01279000d5827e1041441151c0c0084972054fc03c50152f031c506460071cd21578037f0724002f482fdc0449d0a0f60d8b81f7505bd301fd807f0c005283f0703bbee6fb017128193a04f80028fc2fd5841e20b35c09c1c14fc04e560bd0c0a360040f01afe06ab80f3cc0e0f007800b0b40d0841eb600822065aa094f1241582960073049092908f585eb80ba1415a44023f028e4080a60282c02650518b41ccc671480b6602d700b6560609016e183ca1649ae16228028a8484804a94051cc2b0e0035705382852702656a1ca34a4c012a202b358101806d6814f0d0c6281ae302f54032b407130241a03fd401 else (if i<4 then 0x14624aa4c00434257081fd608c4a09e7018ba817934a308074a4113483d450bd50015d4166081913424b80733419f9007fa0c01a13ec8256280239434fa075301d740274104630100fd0d3681a130b88a849a5071302a49033a8154d02fcf80bac069480b9b00da40206708cc4142a81342805fc0092c0ad281e6302166093aa13218087a80d4a05a5208cd42385042f80a758153682831845ac024d80b8001f39853ee02a26139b821dc85c0a058600c22418d30167706534006780fd602d01048ac0944c25a1854ec038c21751d21ee03c2a422fe001701862a19e6060c4035941f3603a6d429f40b08c0b1f023af0558a019a4076a006510183013304106f0158f497a683c48019c0431009c2808d441b7a843ce05faa0f278064705c6c04ba411fec13748310405836112141fc7a586308f7605d240a00011b607f22061a4180c0456f08dba0d064070e021410c0280b3fc173a05ec30185017275055c8181500c501772c17fa8457008f52172101398059350769609ad02f9a832fc063d0157b400fc007da08cba04d081038241b600dba08e2c28ba24a6a0a4aa12f348c17a1b750661883be41f9285f4d0beea0e69c19438000a08bdc183301e0d0299b09e700c4dc2d238129802cba0d35c0e5782f7004b0e02f382d5b05c55017f4113a81ce70549200dea14e04276302787035b8097201ec5812fd064ba01aa00b4d8088e084a4090dd215b85dd20967a0a1ec29178103c0a3cc84868289c0229c04304022f0015d829330a468121d80963a58d207cbc070e810fd837754154607ca01cf28467b0b24802e48266a027bb08e68003f008448528c0130813490012802a19072a005e3404a981daf020f20e6681b82828540bac211e100ca084da203c8a0e1c812f30222504bec06ca42267214da046f20bf850469a19700212a03951054c8018a069de023402b6684d9c00032963fc04fa032bd0884a08ab42a608536a06fe684cfc0023a0b99433e2041a02e53833c8078e0166310ca7805ed73898073a820c10225e05914047e8066484f7c025b89489825510417309eb204ee0010c840904b1c607e681db7803de0aee6100b51f3506146066420d7bc05258063605dec0c01028fd011d1083380849809850446b066f0149d80a45808e2012240f6b01236817590270a174f828e60372d061a8080bd84a501a380b07a03cb82ae600944078a80f7f00db60006a002b410d400cc8850e7052a80e94129f70534a06e601787811b003aa10b3f41559c2e960616905954002c82f778353a0a89613a610a5b00b2e4983604f10157f2120b05f4285a8001db00091096ae01dc8050f05b1d0984a14318137c817f80408296480038a84604047ca9130c182d8244603126184d00f578386f077501262d30a084d520c11a121b4095881c040162c049f41 else 0x380cd405f17486ca126e0207a8168101cf00be0005800383e01a320635001858320d06e24e730020a68210f4323e063b01ca303f3707b3043f7c225f816da052e60107010d5002090b39a02ad02b8281fb60c2ee0d5c10cb100962029d813c5030510188500abe094a82ef1030a9055040ba901f7c80ced0b4b4065ec1f278116c08b001217c258aa0c500a2c2099a419678568502b58968759a7d029030b2160d2ec02c5010eb05a7c0f2d4036783276055c6175702ad800da807e2200d2808bd0546d4bc1e0df592c9b02017066c40bb8d054481d0b0992e94700228983c0501f0084bec17b780400098b210a3c0f58841fa0a832169e0102a804db06a5815c99267883ad90bb1a16b882f29035a6043a6054300f9ca11fa00c02109b90cde80ec60aa98104c4130f81f0202f880c2c40c2e80eee047e4111e0029b05b0a237ee09ab42ccea544f0a5de0cfbc23bca14af0a7761176414a581c410af9a099342ae9a129307c64158f02ab88143a0a65c983640c51841cb0aea603a74125404ced06eaa132f180cf23b0f089ac10a8506d6006bc02dd60ace02d7a835c10a1a8131e1913785b700070c05a90254902cee0c25815f64109b3304a01fa20e3e8044d80562034d607a642ffb019f30440c10b60043600fa0044fe0bc2816a30011749a0a0a8b8246c03072083461440423b3009ae0bf14146b423ad850180aeca053f01ac9240b70a97a037cc1fdb0291f4978608648047e0318d06f3a14134276c040630a8e0142282d16018fd0416213e8d091e04f84097ca038f8049d013d80a8600d3c411a7823da09d021299403b3a0f3d0a52682888176e8311309be4096841fa2017d501ee407b4025d1809b100eb20202c25eb846874168c92fdc302b0515f0b674022a0091d043d50062a0356816de016fb05ac0960cc0f12809e600e180eb1808a202da9091600f6d019c5811e7099ec0a07c1e77835f205cb60e4d5095c032640ade40b67c28188492d01d46911fc1fff257d90708084aa90ca880c3109a1205ce524c78412c077ba056f5262882095068e490b6d0ce1824700a6b0124102de7a4ceb010ee044dc06ba84bf408e2a0ae44170a0415f00e50040b4220d8054e05b14159c024f90354d09b18036040c8101c8d05aa60f0c81eaa00de043430095d025de80d9202ac40f8a41a1f833db0053e15fa8298a005dc07a74122600d2a8224b00e7a0f23d99e18376106fd00e8ac197602fbb0b1741635c13b903de107d141611830168)))
def oH9 (h : Nat) : Option (Nat × Nat):=lookupWord 589 1765 11 19 11 4 oH9F h
def oP10F (i : Nat) : Nat:=(if i<25 then (if i<12 then (if i<6 then (if i<3 then (if i<1 then 0x87fdcb245a824d20c7f4916c5a824d208efcc66c5a824d20c7edb9889a824d20c7edb9549a824d20a7ecc9549a824d2087fdc96c9a824d20e37c98955a824d20c77cb9955a824d20c77db9955a824d20a3fcc9615a824d20a5fcc7655a824d20a3fcc8655a824d2087fccb655a824d2087fcc96d5a824d2087fdc96d5a824d20a7f4c1659a824d20c5fdb99dda824d2087fdcb65da824d20a3fcc9a21a824d2087fcc9aeda824d20b7dacc4c29924d20f7c93054a9924d20e7e9a054a9924d20f759309569924d20e779a09569924d20e7d9306969924d20e76d526969924d20f6d93099a9924d20e6f9a099a9924d20e6ed5269a9924d20e67e5569a9924d20c6fcb569a9924d20c6fcb869a9924d20a6fecc69a9924d20e5ed5269e9924d20e57e5569e9924d20e4fe6669e9924d20c5fcb869e9924d20f3d930a229924d20e3f9a0a229924d20e2fda6a229924d20e1fda7a229924d20c77e556ea9924d2087fcc56ea9924d20c6fe666ea9924d20c3fe886ea9924d2087fcc86ea9924d20ef61105455224d20ef49305495324d2085fdc7aed9524d2087f5caaed9124520efa1a44414224520d5e4b74859524520af72cc441a524520ef6110889a524520ef6110509a524520ef61106c9a524520ef51108cda524520a73cc464da524520a76dc22e5a524520a73dc42e5a524520a67dc62e5a524520cf7110aeda524520ef6110549a524520a57cc7655a524520a4fcc7655a624520edc52168e7724520ed71106967724520ede200485a724520ede130485a724520ade6cc485a724520edc5218cda724520a5bcc464da724520eda521911a724520ed6521955a724520e5e521655a72452085fccb655a724520cde521aeda724520eb71106968824520e9e52169e8824520e375816959824520e2f5816999824520a1fcc7655a824520e771106969924520e5e52169e992452083fdcaaed9826120c7d9a06cc9124d20c6dda66cc9124d20c779a06d49124d20c67da66d49124d20c6f9a06d89124d20c5f9a06dc9124d20c4fda66dc9124d20c3f9a06e09124d20c2fda66e09124d20efc130485a124d20a7e5c2245a124d20a7b5c4245a124d20a775c5245a124d20a3f5c8245a124d2087f9c02e5a124d2087ddcaaed9324d20ef4930549a524d20a76dc2255a524d20a73dc4255a524d20c7f1a02c59624d20c6f5a62c59624d20a6f8c9441a624d20a6ecc9485a624d20a6edc2255a624d20a6bdc4255a624d2086fdcb255a624d20a4fcc7655a624d20a5f9c0245a724d20a5edc2245a724d20a5ddc3245a724d20a5bdc4245a724d20a57dc5245a724d20a4fdc6245a724d20a1fdc8245a724d2085fdcb245a724d208deccb549a724d20ade5c12c9a724d20adadc42c9a724d20ad6dc52c9a724d2085fccb655a724d20a5f4c1659a724d20 else (if i<2 then 0xa3fdc96868824d20fbc93088a8824d20fbc93054a8824d20ebe9a054a8824d20b3ecc954a8824d20f3da0064e8824d20f3d97064e8824d20f3d61164e8824d20e3dda164e8824d20f3ce2264e8824d20b3decc64e8824d20fb59309568824d20eb79a09568824d20f35d939568824d20e3f9a06568824d20b1fcc76568824d20ebd9306968824d20eb6d526968824d20e37c956968824d20a3fcc96968824d20a3fdc96968824d20fad93099a8824d20eaf9a099a8824d20f2dd9399a8824d20e3f9a065a8824d20b3f4c165a8824d20e2fda665a8824d20eafa0069a8824d20eaf91069a8824d20eaf97069a8824d20eaf61169a8824d20eaed2169a8824d20e2fd9169a8824d20eaee2269a8824d20eaed5269a8824d20ea7e5569a8824d20e2fc9569a8824d20e2fd9569a8824d20e2fcc969a8824d20aafecc69a8824d20f9d9309de8824d20f1dd939de8824d20e8fda69de8824d20f3d93065e8824d20e2fda665e8824d20e1fda765e8824d20e9fa0069e8824d20e9f91069e8824d20e9f61169e8824d20e9ed2169e8824d20e1fc9169e8824d20e1fd9169e8824d20e9ee2269e8824d20e9dd3269e8824d20e9ed5269e8824d20e9ecc269e8824d20e97e5569e8824d20e1fd9569e8824d20e8fe6669e8824d20e1fd9669e8824d20a9fecc69e8824d20e3f9a02e68824d20b3ddc32e68824d20e2fda62e68824d20b2fdc62e68824d20e1fda72e68824d20c6fcb969a8824d20c5fcb969e8824d20e7f1a08459824d20e3f9a06059824d20e3f5816859824d20c7f9a06c59824d2096fcc66c59824d20e7e9a05499824d20d76cb55499824d2097eccb5499824d20e779a09559824d20e76d526959824d20c77cb56959824d2087fccb6959824d20c7f9a06d59824d2095fcc76d59824d20e6f9a09999824d20e6fa006999824d20e6f6116999824d20e2fd816999824d20c6fdb16999824d20e6ee226999824d20e6ed526999824d20e67e556999824d20c6fcb56999824d20c6fdb56999824d20c6fccb6999824d20a6fecc6999824d20c7f9a06d99824d2097f4c16d99824d20c6fda66d99824d20e4fda69dd9824d20e5fa0069d9824d20e5f61169d9824d20e1fd8169d9824d20c5fdb169d9824d20e5ee2269d9824d20e5dd3269d9824d20e5ed5269d9824d20e57e5569d9824d20c5fdb569d9824d20e4fe6669d9824d20c5fdb669d9824d20a5fecc69d9824d20977cc56dd9824d20c6fda66dd9824d20e3f9a0a219824d20e2fda6a219824d20e1fda7a219824d20c7f9a0aed9824d20c6fda6aed9824d20c5fda7aed9824d2087fdcaaed9824d20a7f9c0245a824d20e3f581245a824d20a7edc2245a824d20a7ddc3245a824d20a7bdc4245a824d20a77dc5245a824d20a6fdc6245a824d20a5fdc7245a824d20a3fdc8245a824d20 else 0xede5216867724d20a5fdc96867724d20fdc93054a7724d20f5d61164e7724d20e5dda164e7724d20b5decc64e7724d20fd59309567724d20f55d939567724d2095fccb6567724d20edd9306967724d20ed6d526967724d20fcd93099a7724d20f4dd9399a7724d20b5f4c165a7724d20ecf91069a7724d20ecf61169a7724d20eced2169a7724d20e4fd9169a7724d20eced5269a7724d20ec7e5569a7724d20e4fd9569a7724d20acfecc69a7724d20e4fd9669a7724d20b7dacc4c19724d20f7d1308459724d20e5f5a78459724d20f5d9305c59724d20a5fdc76859724d2087fdcb6859724d20f7c9305499724d20f759309559724d20e7d9306959724d20e76d526959724d20f6d9309999724d20e4fda79999724d20e6f6116999724d20e4fd716999724d20c6fdb16999724d20e6ed526999724d20e67e556999724d20c6fdb56999724d20a6fecc6999724d2097f4c16d99724d20c6fda66d99724d20edf110545a724d20acfcc6605a724d20e5f581245a724d20a5fdc5245a724d20a5fdc8245a724d20edea00549a724d20ede910549a724d20ede611549a724d20ed6d51549a724d20e5ec91549a724d20adedc1549a724d20edcd32609a724d20a5fdc9609a724d20ed7a00955a724d20ed7910955a724d20ed7611955a724d20ed6d21955a724d20e57c91955a724d20e57d91955a724d20e57c98955a724d20a5fcc9595a724d20a5fcc9615a724d20e5fa00655a724d20e5f611655a724d20e57d51655a724d20a5fdc1655a724d20a5fcc8655a724d20c5fccb655a724d20a5fecc655a724d20ecfa00999a724d20ecf910999a724d20ecf611999a724d20eced21999a724d20e4fd91999a724d20ecee22999a724d20ecdd32999a724d20eced52999a724d20ececb2999a724d20ec7e55999a724d20e4fd95999a724d20e5fa00659a724d20e5f910659a724d20e5f611659a724d20e5ed21659a724d20e4fd61659a724d20e5f4c1659a724d20a5fdc1659a724d20e5ee22659a724d20e5dd32659a724d20e5ed52659a724d20e5ecb2659a724d20e57e55659a724d20e4fd65659a724d20a5fdc5659a724d20a5fecc659a724d20cdf910aeda724d20cdf611aeda724d20cded21aeda724d20c5fd91aeda724d20ccfe66aeda724d20c5fd96aeda724d20a7f4c1659a724d20bbdacc4c28824d20e9f9a75c28824d20fbd1308468824d20ebf1a08468824d20fbc9304868824d20ebe9a04868824d20e3f9a02468824d20b3f9c02468824d20b3edc22468824d20b3ddc32468824d20b3bdc42468824d20b37dc52468824d20e2fda62468824d20b2fdc62468824d20b1fdc72468824d2093fdcb2468824d20e3f9a06468824d20ebd9306868824d20abf9c06868824d20ebe5216868824d20e3f4916868824d20a3fcc96868824d20)) else (if i<4 then 0xe6eda64859624d20e6f9a05859624d20a7f9c06859624d20e7e5216859624d20a6fdc66859624d20e7f1a02c59624d20e6f5a62c59624d20c7f9a06c59624d20c6fda66c59624d20e7e9a05499624d20d7e4b15499624d2097eccb5499624d20e779a09559624d20d774b19559624d20e6f9a05959624d20d6f4b15959624d2096fccb5959624d20c7f4b16959624d20c77cb56959624d20a6fdc66959624d2087fccb6959624d2087fdcb6959624d20c7f9a06d59624d2097f4c16d59624d2095fcc76d59624d20c7f9a0aed9624d2097f5c1aed9624d20c6fda6aed9624d2087fdcaaed9624d20eef170845a624d20eee970485a624d20eef110545a624d20ecf9705c5a624d20aef9c05c5a624d20eee5215c5a624d208efccb605a624d20eeea00549a624d20eee910549a624d20eee970549a624d20eee8c0549a624d20eee611549a624d20ee6d51549a624d20aeedc1549a624d20ececc7549a624d20e6ecc9549a624d20aeeecc549a624d20a6fdc9549a624d20a6fdc9609a624d20ee7a00955a624d20ee7910955a624d20ee7970955a624d20ee7611955a624d20ee6d21955a624d20e67c91955a624d20e67d91955a624d20ee6e22955a624d20ee6cc2955a624d20e67c98955a624d20e67cc9955a624d20ee6d52955a624d20aeecc2955a624d20a6fcc9955a624d20ecf9705d5a624d20ee6d525d5a624d20aef9c0215a624d20aef5c1215a624d20aeedc2215a624d20aeddc3215a624d20aebdc4215a624d20acfdc7215a624d20a6fdc9215a624d208efdcb215a624d20a6fcc9615a624d20a6fdcb255a624d20e6fa00655a624d20e6f970655a624d20e6f611655a624d20e67d51655a624d20a6fdc1655a624d20e6ee22655a624d20e67e55655a624d20e4fcc7655a624d20a6fcc8655a624d20a6fccb655a624d20a6fecc655a624d20aeedc22d5a624d20a6fdc92d5a624d20a6fcc96d5a624d20aef9c02e1a624d20aef5c12e1a624d20aeedc22e1a624d20aeddc32e1a624d20aebdc42e1a624d20ae7dc52e1a624d20acfdc72e1a624d20a6fdc92e1a624d20a6fcc96e1a624d20e67e552e5a624d20a6fdc52e5a624d20a6fdc82e5a624d20cefa00aeda624d20cef910aeda624d20cef970aeda624d20cef611aeda624d20ceed21aeda624d20c6fd91aeda624d20ceee22aeda624d20ceed52aeda624d20ce7e55aeda624d20c6fc95aeda624d20c6fd95aeda624d20c6fcb9aeda624d20e6f996801a624d20e6ed96889a624d20e67d96955a624d20a6fcc9595a624d20a7edc2255a624d20a7bdc4255a624d20a6fdc6255a624d2087fdcb255a624d20a6fdc6655a624d20a5fcc7655a624d2087fcc96d5a624d20bddacc4c27724d20fdd1308467724d20fdc9304867724d20edd9306867724d20adf9c06867724d20 else (if i<5 then 0xff49305497524d20fd69705497524d20ed6da75497524d20f5d97064d7524d20df99b44c08524d20cdf9a76c08524d20dfd1306c48524d20cff1a06c48524d20cdf5a76c48524d20dfc9306c88524d20cfe9a06c88524d20cdeda76c88524d20d7d9b064c8524d20d7d5b164c8524d20d7cdb264c8524d20d79db464c8524d20cfd9a06cc8524d209fd9c06cc8524d20cddda76cc8524d20ded9306d88524d20cef9a06d88524d20d6dd936d88524d20ccfda76d88524d20ddd9306dc8524d20cdf9a06dc8524d20d5dd936dc8524d20d7d9306e48524d20c7f9a06e48524d2097ddc36e48524d20c5fda76e48524d20cfd9306e88524d208ff9c06e88524d20c7dd936e88524d208dfdc76e88524d20d7d8b94c18524d20e7f1a08459524d20d5f4b78459524d20e779a05459524d20e775516859524d20c5fcb76859524d20c7f9a06c59524d2095fcc76c59524d20e5eda78899524d20e5dda74c99524d20e779a09559524d20e57da79559524d20c7f9a0aed9524d2095fdc7aed9524d2087fdcaaed9524d20c7f9b9801a524d20afdacc4c1a524d20efd130845a524d20c7f5b9845a524d20efc930485a524d20ef7110545a524d20ef5930545a524d20c77db9545a524d20a7f9c0245a524d20a7edc2245a524d20a7ddc3245a524d20a7bdc4245a524d20a77dc5245a524d20a6fdc6245a524d20a5fdc7245a524d20a3fdc8245a524d20cfd9306c5a524d2087fdc96c5a524d20efc930889a524d20c7edb9889a524d20ef6a00549a524d20ef6910549a524d20ef4d30549a524d20ef6970549a524d20ef68c0549a524d20ef6611549a524d20cf6db1549a524d20af6dc1549a524d20cf6db7549a524d20ed6cc7549a524d20e76cb9549a524d20e76cc9549a524d20af6ecc549a524d20efc930549a524d20ef5930549a524d20ef5930955a524d20a77cc9955a524d20ef5930615a524d20a77cc9615a524d20cfd930aeda524d20cf6d52aeda524d20c77c95aeda524d2087fcc9aeda524d20bedacc4c26624d20ecf9a75c26624d20fed1308466624d20eef1a08466624d20fec9304866624d20eee9a04866624d20e6f9a06466624d20eed9306866624d20aef9c06866624d20eee5216866624d20fec93088a6624d20fec93054a6624d20eee9a054a6624d20f6da0064e6624d20f6d97064e6624d20f6d61164e6624d20e6dda164e6624d20f6ce2264e6624d20b6decc64e6624d20fe59309566624d20ee79a09566624d20f65d939566624d20b6edc22566624d20e4fda72566624d20e6f9a06566624d20b4fcc76566624d20eed9306966624d20ee6d526966624d20e67c956966624d20a6fcc96966624d20a6fdc96966624d20e6f9a64419624d20e7f1a08459624d20e6f5a68459624d2097f4cb8459624d20e7e9a04859624d20 else 0xc77e556ea992612087fcc56ea9926120bfc8c26d53024d20b7d8c96d53024d20bfc8c26d93024d20b7d8c96d93024d20bfc8c26e13024d20b7d8c96e13024d20bfd2cc4c21124d20edf1a75c21124d20bfcacc4c12124d20ede9a75c12124d20ffc1304857124d20fde1704857124d20ede5a74857124d20ded8b64c18124d20e7f1a06049124d20e6f5a66049124d20d7d5816cc9124d20d775816d49124d20c77dca6d49124d20977ecc6d49124d20c7f9a06d49124d20c6fda66d49124d20d6f5816d89124d20c3fdca6e09124d2093fecc6e09124d20c7f9a06e09124d20c6fda66e09124d20afdacc4c1a124d20cdf9b75c1a124d208ff9cb5c1a124d20efe170485a124d20cfe5b7485a124d20efd130545a124d20cff1b0545a124d20efd130605a124d20a7f5c5245a124d20a7f5c8245a124d20bfcacc4c22224d20bfcacc4c15224d20bfc9c32c15224d20afe9ca2c15224d20ffc1308455224d20efe1a08455224d20ff61105455224d20ff49305455224d20ef69a05455224d20e7e9a02455224d20b7e9c02455224d20b7cdc32455224d20b6edc62455224d20b5edc72455224d20b3edc82455224d20efc9306855224d20afe9c06855224d20ef65516855224d20e7e4916855224d20a7ecc96855224d20dfc9306c55224d20cfe9a06c55224d20cfe5a16c55224d20fdc9302dd5224d20adedca2dd5224d20dfc930aed5224d20cfe9a0aed5224d20cdeda7aed5224d20edcda74c95224d20c5fda76e55224d20f7d1708459324d20f5d9705c59324d20b6dcc66059324d20e7d5516859324d20e7d5816859324d20b5dcc76d59324d20b7d4c16d99324d20d7da00aed9324d20d7d970aed9324d20d7d611aed9324d20c7dda1aed9324d20d7ce22aed9324d20d79dc4aed9324d20c7ddcaaed9324d20b7d9c0aed9324d20b7cdc2aed9324d20b79dc4aed9324d20a7ddcaaed9324d209fd9c0aed9324d209fcdc2aed9324d208fddcaaed9324d20bf5acc4c25524d20ff51308465524d20ef71a08465524d20ff49304865524d20ef69a04865524d20e779a02465524d20b779c02465524d20b76dc22465524d20b75dc32465524d20b73dc42465524d20b67dc62465524d20b57dc72465524d20b37dc82465524d20977dcb2465524d20e779a06465524d20ef59306865524d20af79c06865524d20ef65216865524d20e774916865524d20a77dc96865524d20ff493088a5524d20ed6da788a5524d20ed5da74ca5524d20ff49302ca5524d20ed6da72ca5524d20f75a0064e5524d20f7597064e5524d20f7561164e5524d20e75da164e5524d20f74e2264e5524d20b75ecc64e5524d20e779a02e65524d20b75dc32e65524d20e57da72e65524d20dfc8b24c25524d20ff493054a5524d20ef69a054a5524d20ed6da754a5524d20))) else (if i<9 then (if i<7 then 0xe1fe77661a824520a3fdc7661a824520a3fecc661a824520c3fd98aeda82452087fcc9aeda824520d3f4b8606992452097f4cb6069924520f7e11054a9924520e7e9a054a9924520f771109569924520e779a09569924520f765219569924520e76da29569924520a77dca9569924520e779306969924520e775816969924520e76dc26969924520e75e336969924520c77cb36969924520c77cb86969924520a77ecc6969924520e7f1106969924520e76d526969924520a7edc26969924520c77cb56969924520e6f58169a9924520e6ed5269a9924520e67e5569a9924520c6fcb569a9924520c6fcb869a9924520e5f93069e9924520e5ed5269e9924520e5de3369e9924520c5fcb369e9924520e57e5569e9924520c5fcb569e9924520c5fcb869e9924520f3e521a229924520e3eda2a229924520e37da5a229924520e2fda6a229924520e1fda7a229924520a3fdcaa229924520e3ed526a29924520e37e556a29924520c3fcb56a29924520a3fecc6a29924520c3fcb86a2992452087fccb6a29924520c7f5816ea9924520c77e556ea992452087fcc56ea9924520c3fe886ea992452087fcc86ea9924520ede5a74857126120ffa1105054226120ff61105455226120ef65516855226120cdedba2dd5226120ff49305495326120d76cb95495326120fda9705097426120b778c94425526120b778c94c25526120b76cc94865526120e774916865526120a77cc96865526120b37dc82e65526120fd69705497526120ed6da75497526120d5f4b78459526120e775516859526120c5fcb7685952612095fcc76c59526120d5dcb78cd952612095fcc76cd952612095fdc7aed952612087fdcaaed9526120a7f8c9441a526120a7f8c94c1a526120a7ecc9485a526120ef7110545a526120e75c958cda526120c7ddb98cda526120ef593054da526120a77cc954da526120a7bcc464da526120a77cc564da52612087fccb64da52612087fdc96cda526120a77cc9955a526120b5bcc464e7726120a5fdc968e772612095fccb656772612087fdcb68d972612097bcc46cd9726120a7bcc464da726120e3f5516859826120b3eccb8899826120b3edc214d9826120a3fdca14d9826120f37a009559826120f376119559826120e37da19559826120f36e229559826120f35e339559826120b3bdc42d59826120b2fdc62d59826120b1fcc76d59826120f1f6119dd9826120e1fda19dd9826120f1de339dd9826120f1be449dd9826120f17e559dd9826120b37cc56dd9826120d3f611aed9826120c3fda1aed9826120d3ee22aed9826120d3edc2aed982612093fdc2aed9826120d37e55aed9826120d1fe77aed9826120c3fdcaaed9826120b3edc2aed9826120a3fdcaaed98261209bedc2aed98261208bfdcaaed9826120c7ed526ea9926120 else (if i<8 then 0xe5f93069d9824520e5f52169d9824520e5ee2269d9824520e5ed5269d9824520e5de3369d9824520c5fcb369d9824520c5fdb369d9824520e5be4469d9824520e57e5569d9824520c5fcb569d9824520c5fdb569d9824520a5fecc69d9824520c7eda26dd9824520c7dda36dd9824520c7bda46dd9824520c77da56dd9824520977cc56dd9824520c6fda66dd9824520d3f5b1a219824520e3eda2a219824520e37da5a219824520e2fda6a219824520e1fda7a219824520d3f581aed9824520c7eda2aed9824520c77da5aed9824520c6fda6aed9824520c5fda7aed982452087fdcaaed9824520ef71106959824520eb75816959824520eaf5816999824520ede52169d9824520ebe970509a824520ebea00549a824520ebe930549a824520ebe970549a824520ebe8c0549a824520e9ecc7549a824520e3ecc9549a824520abeecc549a824520a3fdc9549a824520abedc214da824520a3fdc914da824520eb6d5254da824520a3fcc954da824520ebad42551a824520abedc2551a824520ebad425d1a824520eb7a00955a824520eb7930955a824520eb7970955a824520eb6e22955a824520eb6d42955a824520eb6cc2955a824520eb5e33955a824520e37cb9955a824520e37cc9955a824520eb6d52955a824520abecc2955a824520a3fcc9955a824520e9f9705d5a824520eb6d525d5a824520e3fa00655a824520e3f970655a824520e3ee22655a824520e3ed42655a824520e3de33655a824520a3fcc3655a824520a3fdc3655a824520e37e55655a824520e1fcc7655a824520a3fccb655a824520a3fecc655a824520abf9c02d5a824520abedc22d5a824520abddc32d5a824520abbdc42d5a824520aafdc62d5a824520a9fdc72d5a824520a3fcc96d5a824520e9f9309dda824520e9ed429dda824520e9ed529dda824520e9de339dda824520e1fd939dda824520e9be449dda824520e97e559dda824520e1fd959dda824520e3f93065da824520e3ed5265da824520e3de3365da824520e1fd7365da824520a3fdc365da824520e3be4465da824520a3fdc465da824520e37e5565da824520a3fdc565da824520cbee22aeda824520cbed42aeda824520cbed52aeda824520cb7e55aeda824520c3fd95aeda824520c9fe77aeda824520c3fd97aeda824520c3fcc9aeda824520a3fcc9aeda824520a3fdc9609a824520e37c98955a824520abf9c0215a824520abf5c1215a824520abedc2215a824520abddc3215a824520abbdc4215a824520aafdc6215a824520a9fdc7215a824520a3fdc9215a824520a3fcc9615a824520a5fcc7655a824520a3fcc8655a82452087fccb655a82452087fcc96d5a824520a3fcc9a21a824520e3ee22661a824520e3ed52661a824520e37e55661a824520a3fcc5661a824520a3fdc5661a824520 else 0xfbe11050a8824520ebe9a050a8824520ebada450a8824520cbedba50a8824520fbe11054a8824520ebe9a054a8824520f3e59154a8824520cbedba54a8824520fb71109568824520eb79a09568824520fb65219568824520f375919568824520eb6da29568824520cb7dba9568824520ab7dca9568824520f3f1106568824520e3f9a06568824520f3e5216568824520e3eda26568824520b1fcc76568824520c3fdba6568824520eb7a006968824520eb75106968824520eb79306968824520eb79706968824520eb6e226968824520eb6d426968824520eb6dc26968824520eb5e336968824520e37d936968824520e37cc96968824520ab7ecc6968824520ebf1106968824520eb6d526968824520abedc26968824520e37d956968824520eaee2269a8824520eaed4269a8824520eaed5269a8824520ea7e5569a8824520e2fd9569a8824520f9f1109de8824520f9e5219de8824520f1f5919de8824520e9eda29de8824520e9dda39de8824520e97da59de8824520e8fda69de8824520c9fdba9de8824520e3eda265e8824520e3dda365e8824520e37da565e8824520e2fda665e8824520e1fda765e8824520c3fdba65e8824520e9fa0069e8824520e9f93069e8824520e9f52169e8824520e9ee2269e8824520e9ed4269e8824520e9ed5269e8824520e9de3369e8824520e1fd9369e8824520e9be4469e8824520e1fd9469e8824520e97e5569e8824520e1fd9569e8824520a9fecc69e8824520ebe52169e8824520b3f5c12e68824520e3eda22e68824520e37da52e68824520e2fda62e68824520e1fda72e6882452097f4cb6468824520ef71106968824520eb75816968824520c77cb96968824520eaf58169a8824520c6fcb969a8824520ede52169e8824520c5fcb969e8824520b3f6cc605982452097f6cc6c59824520f3e5818899824520d7e5b18899824520e7e9a05499824520f3e5815499824520d7e5b1549982452097eccb5499824520e779a09559824520f375819559824520d775b19559824520e76da29559824520a77dca9559824520e77a006959824520e775106959824520e779306959824520e775816959824520e76e226959824520e76dc26959824520e75e336959824520c77cb36959824520c77ccb6959824520a77ecc6959824520e3f5816959824520e76d526959824520a7edc26959824520c77cb5695982452087fccb6959824520c7f9a06d59824520c7eda26d59824520c7dda36d59824520c77da56d5982452095fcc76d59824520e6f5816999824520e6ee226999824520e6ed526999824520e67e556999824520c6fcb56999824520c6fdb56999824520f1f5819dd9824520d5f5b19dd9824520e5eda29dd9824520e5dda39dd9824520e57da59dd9824520e4fda69dd9824520e5fa0069d9824520)) else (if i<10 then 0xe76d526959724520a7edc26959724520c7eda26d59724520c7dda36d59724520c77da56d59724520e6f9306999724520e6f5816999724520e6ed526999724520e6de336999724520e4fd736999724520c6fdb36999724520e6be446999724520c6fdb46999724520e67e556999724520c6fdb56999724520ede8c24c1a724520edb8c44c1a724520e5f8c94c1a724520adfacc4c1a724520ede530485a724520ede550485a724520ede580485a724520ede5c3485a724520ede5c4485a724520ede5c5485a724520ede5c8485a724520edf130485a724520ede930889a724520ede5214c9a724520a5fdc94c9a724520ede930509a724520edea00549a724520ede930549a724520ede521609a724520a5fdc9609a724520edda008cda724520edd8c08cda724520edd5218cda724520edce228cda724520edcd428cda724520edcd528cda724520e5dc988cda724520e5dcc98cda724520edd9308cda724520adf8c08cda724520ede5218cda724520a5fcc98cda724520edd93050da724520ede52150da724520edad4250da724520edd93054da724520ede52154da724520ed6d5254da724520a5fcc954da724520adf9c020da724520ede52120da724520adf5c120da724520adedc220da724520adbdc420da724520ad7dc520da724520acfdc620da724520a5fdc920da7245208dfdcb20da724520ede52160da724520a5fcc960da724520e5fa0064da724520e5f52164da724520e5ee2264da724520e5ed4264da724520e5de3364da724520e5bcc464da724520a5fcc564da724520a5fcc864da724520a5fccb64da724520a5fdcb64da724520a5fecc64da724520ede52164da724520edb930911a724520edad52911a724520ed9e33911a724520e5bd93911a724520ede521551a724520edad42551a724520adedc2551a724520ede521611a724520e5f930651a724520e5ed52651a724520e5de33651a724520a5fdc3651a724520e5bd54651a724520a5fdcb651a724520ed7a00955a724520ed7930955a724520ed6d42955a724520ed5e33955a724520e57d93955a724520ed3e44955a724520e57d94955a724520e57c98955a724520ede521615a724520a5fcc9615a724520e5fa00655a724520e5ed42655a724520e5de33655a724520a5fcc3655a724520a5fdc3655a724520e5be44655a724520a5fdc4655a724520a5fcc8655a724520c5fccb655a724520a5fecc655a724520ede521655a724520cdf930aeda724520cded42aeda724520cdde33aeda724520c5fd93aeda724520cdbe44aeda724520c5fd94aeda724520efe130485a724520efc5218cda724520a7bcc464da724520efa521911a724520bbe6cc4868824520b3f4cb6468824520b3f6cc6468824520fbe11088a8824520f3e59188a8824520cbedba88a8824520 else (if i<11 then 0xaeedc2551a624520eead425d1a624520ee7a00955a624520ee7930955a624520ee7970955a624520ee7581955a624520ee6e22955a624520ee6d42955a624520ee6cc2955a624520ee5e33955a624520e67c98955a624520e67cc9955a624520ee6d52955a624520aeecc2955a624520a6fcc9955a624520ecf9705d5a624520ee6d525d5a624520aef9c0215a624520aef5c1215a624520aeedc2215a624520aeddc3215a624520aebdc4215a624520acfdc7215a624520a6fdc9215a6245208efdcb215a624520a6fcc9615a624520e6fa00655a624520e6f970655a624520e6f581655a624520e6ee22655a624520e6ed42655a624520e6de33655a624520a6fcc3655a624520a6fdc3655a624520e67e55655a624520e4fcc7655a624520a6fcc8655a624520a6fecc655a624520bdf2cc4427724520ede9a24c27724520fde1304867724520f5f1306467724520b5f6cc6467724520fde11050a7724520edada450a7724520fde11054a7724520f5e59154a7724520fdd1108ce7724520fdc5218ce7724520f5d5918ce7724520edcda28ce7724520adddca8ce7724520f5f11064e7724520f5e52164e7724520e5eda264e7724520b5bcc464e7724520edd9c068e7724520edd58168e7724520edcd4268e7724520edcd5268e7724520addecc68e7724520edd93068e7724520adf9c068e7724520ede52168e7724520e5dd9368e7724520fda5219127724520f5b5919127724520fd71109567724520fd65219567724520f575919567724520ed6da29567724520ed5da39567724520f5f1106567724520f5e5216567724520e5eda26567724520e5dda3656772452095fccb6567724520ed79306967724520ed75816967724520ed6d426967724520ed6dc26967724520ed5e336967724520e57d936967724520ed3e446967724520ad7ecc6967724520edf1106967724520ed6d526967724520adedc26967724520e57d956967724520ecf93069a7724520ecf58169a7724520eced4269a7724520eced5269a7724520ecde3369a7724520e4fd9369a7724520ecbe4469a7724520ec7e5569a7724520e4fd9569a7724520ede5a74858724520efc52168d8724520ef71106958724520e7e9a24c19724520e7cda28cd9724520e5dda78cd9724520a7ddca8cd9724520e5eda25cd9724520e7d58168d9724520e7cd5268d9724520e5ddc768d9724520a7decc68d9724520e5dd7368d9724520a5fdc768d9724520c7eda26cd9724520c7dda36cd972452097bcc46cd9724520e79da39119724520e5bda79119724520e76da29559724520e75da39559724520e779306959724520e775816959724520e76dc26959724520e75e336959724520e57d736959724520c77db36959724520e73e446959724520c77db46959724520a77ecc6959724520 else 0xaf3dc42e1a524520ae7dc62e1a524520ad7dc72e1a524520ef71106e1a524520a77cc96e1a524520e779302e5a524520e775812e5a524520e75e332e5a524520a77dc32e5a524520a77dc82e5a524520cf7a00aeda524520cf7510aeda524520cf7930aeda524520cf7970aeda524520cf7581aeda524520cf6e22aeda524520cf6d42aeda524520cf6cc2aeda524520cf5e33aeda524520c77d93aeda524520c77c98aeda524520c77cc9aeda524520ef7110aeda524520cf6db2aeda524520af6cc2aeda524520a77cc9aeda524520cfe9b2801a524520cff1b4441a524520ef71c5441a524520aff2cc441a524520ef7110541a524520efe110889a524520efe110509a524520cfadb4509a5245208fedcb509a524520ef6a00549a524520ef6510549a524520ef6930549a524520ef6970549a524520ef68c0549a524520ef6581549a524520cf6db7549a524520ed6cc7549a524520e76cc9549a524520af6ecc549a524520efe110549a524520ef7110549a524520a77dc9549a524520cfe9306c9a524520cfe9706c9a524520cdecc76c9a5245208feecc6c9a524520efe1106c9a524520efd1108cda524520ef4d528cda524520cfcdb28cda524520ef711014da524520af79c014da524520af6dc214da524520a77dc914da524520ef711054da524520ef593054da524520cf6db254da524520a77cc954da524520a7bcc464da524520a77cc564da52452087fccb64da524520cf6d526cda52452087fcc96cda524520ef7110551a524520ef2d42551a524520af6dc2551a524520ef7110955a524520cf6db2955a524520af6cc2955a524520a77cc9955a524520ef71105d5a524520ed79705d5a524520cf6db25d5a524520ef7110215a524520af79c0215a524520af75c1215a524520af6dc2215a524520af5dc3215a524520af3dc4215a524520ae7dc6215a524520ad7dc7215a524520a77dc9215a524520ef7110615a524520a77cc9615a524520e77a00655a524520e77510655a524520e77970655a524520e77581655a524520e76e22655a524520e75e33655a524520a77cc3655a524520a77dc3655a524520e57cc7655a524520a77cc8655a524520a77ecc655a524520ef7110655a524520cff110aeda524520cf6d52aeda5245208fecc2aeda524520c77d95aeda52452087fcc9aeda524520e6f5c9605a624520aef6cc605a624520eee581889a624520eee970509a624520eee581509a624520eeea00549a624520eee930549a624520eee970549a624520eee8c0549a624520eee581549a624520ececc7549a624520e6ecc9549a624520aeeecc549a624520a6fdc9549a624520eaf581609a624520a6fdc9609a624520aeedc214da624520a6fdc914da624520ee6d5254da624520a6fcc954da624520eead42551a624520)))) else (if i<18 then (if i<15 then (if i<13 then 0xf7e1108899524520e5eda78899524520f7e1105099524520e7e9a05099524520d5ecb75099524520f7d1108cd9524520e7d9a08cd9524520f7c5218cd9524520e7cda28cd9524520d5dcb78cd9524520a7ddca8cd9524520d7e5216cd9524520c7eda26cd952452095fcc76cd9524520f771109559524520e779a09559524520f765219559524520e76da29559524520e57da79559524520f5f1102dd9524520f5e5212dd9524520e5eda22dd9524520d7f110aed9524520c7f9a0aed9524520d7e521aed9524520c7eda2aed952452095fdc7aed952452087fdcaaed9524520ef71c3441a524520ef71c7441a524520ef71c8441a524520ef68c24c1a524520ef38c44c1a524520e778c94c1a524520af7acc4c1a524520ef71104c1a524520ef7110601a524520ef71106c1a524520ef7200605a524520ef7130605a524520ef7170605a524520eb7580605a524520af75c0605a524520e775c9605a524520af76cc605a524520ef6930889a524520ef6581889a524520ef71104c9a524520a77dc94c9a524520ef6930509a524520ef6970509a524520ef6581509a524520ef7110609a524520eb7581609a524520a77dc9609a524520ef6a006c9a524520ef65106c9a524520ef69306c9a524520ef69706c9a524520ef68c06c9a524520ef65816c9a524520ed6cc76c9a524520e76cc96c9a524520af6ecc6c9a524520ef71106c9a524520ef5a008cda524520ef55108cda524520ef59708cda524520ef58c08cda524520ef55818cda524520ef4e228cda524520ef4d428cda524520ef4db28cda524520e75c988cda524520e75cc98cda524520ef71108cda524520ef59308cda524520af78c08cda524520a77cc98cda524520ef711050da524520ef593050da524520ef2d4250da524520ef71105cda524520ed79705cda524520af79c05cda524520ef711020da524520af79c020da524520af75c120da524520af6dc220da524520af3dc420da524520ae7dc620da524520ad7dc720da524520a77dc920da5245208f7dcb20da524520ef711060da524520a77cc960da524520e77a0064da524520e7751064da524520e7797064da524520e7758164da524520e76e2264da524520e76d4264da524520e75e3364da524520e73cc464da524520a77cc864da524520a77ccb64da524520a77ecc64da524520ef711064da524520ef71102cda524520af79c02cda524520af6dc22cda524520ef71106cda524520ef59306cda524520cf6db26cda524520a77cc96cda524520ef71105d1a524520ed79705d1a524520ef2d425d1a524520ef71106d1a524520ef2d426d1a524520af6dc26d1a524520ef71106dda524520ed79706dda524520cf6db26dda524520ef71102e1a524520af79c02e1a524520af6dc22e1a524520af5dc32e1a524520 else (if i<14 then 0xc5fda76e45324520cfe5216e85324520c7f5916e853245208fedc26e85324520ff61105495324520ff49305495324520ef69a05495324520f765915495324520efb1a44415424520ffa1105095424520efa9a05095424520dfe1106c95424520cfe9a06c95424520ede5a74857424520ffa1105097424520fda9705097424520edada75097424520cf79ba8025524520bf72cc4425524520ef69a24c25524520cf79ba4c25524520ef69a25c25524520ff62004865524520ff61304865524520ff61704865524520ef65a74865524520bf66cc4865524520ed75a74865524520f772006465524520f771306465524520b776cc6465524520ff611088a5524520f7659188a5524520ed6da788a5524520cf6dba88a5524520ff611050a5524520ef69a050a5524520ef2da450a5524520cf6dba50a5524520ff61102ca5524520f765912ca5524520bf65c12ca5524520ed6da72ca5524520af6dca2ca5524520ff45218ce5524520f755918ce5524520ef4da28ce5524520af5dca8ce5524520f771102e65524520e779a02e65524520f765212e65524520b775c12e65524520e76da22e65524520e57da72e65524520dfe0b24425524520d7f0b94425524520ede5a74865524520d7e4b94865524520d7e4b26465524520ff611054a5524520ef69a054a5524520f7659154a5524520ed6da754a5524520ede9a25c17524520fde1704857524520ede5a74857524520ff61105497524520fd69705497524520f765915497524520ed6da75497524520cfe9a26c08524520cdf9a76c08524520dfe1b04848524520ede5a74848524520d7f1b06448524520cff1a06c485245209ff1c06c48524520cfe5a26c48524520cdf5a76c48524520dfe1106c88524520cfe9a06c88524520d7e5916c885245209fe5c16c88524520cdeda76c88524520dfd1106cc8524520cfd9a06cc8524520dfc5216cc8524520d7d5916cc8524520cfcda26cc8524520cddda76cc8524520dfb1106d08524520cfb9a06d08524520dfa5216d08524520d7b5916d08524520cfada26d08524520cdbda76d08524520def1106d88524520cef9a06d88524520dee5216d88524520d6f5916d88524520ceeda26d88524520ccfda76d88524520ddf1106dc8524520cdf9a06dc8524520dde5216dc8524520d5f5916dc8524520cdeda26dc8524520d7f1106e48524520c7f9a06e48524520d7e5216e4852452097f5c16e48524520c7eda26e48524520c5fda76e48524520cff1106e885245208ff9c06e88524520cfe5216e88524520c7f5916e885245208fedc26e885245208dfdc76e88524520b7f2cc4419524520e7e9a25c19524520f7e2004859524520f7e1704859524520e7e5a74859524520d7e4b74859524520b7e6cc4859524520e5f5a74859524520d5f4b76059524520 else 0xef56118ce5524d20ef4d218ce5524d20e75d918ce5524d20c7f4b98458524d2087fccb6458524d20ef593054d8524d20c7f4b88459524d20e775516059524d2087fccb6059524d2087fcc86c59524d2087fecc6c59524d20e7d6118cd9524d2087fccb60d9524d2087fcc86cd9524d2087fecc6cd9524d20c3fcb86e19524d20c7f9c0aed9524d20c7f611aed9524d20c77d51aed9524d2087fdc1aed9524d20c7de33aed9524d2087fdc3aed9524d20c77dc5aed9524d20c5fdc7aed9524d2087fcc8aed9524d2087fdc8aed9524d20a7f9c0aed9524d20a7edc2aed9524d20a77dc5aed9524d20a5fdc7aed9524d20ef71105459524d208ff9c0aed9524d208fedc2aed9524d208dfdc7aed9524d20abeecc4868824d20ebf1105468824d20a3fecc6468824d20ebe91054a8824d20ebe93054a8824d20ebe61154a8824d20eb6d5154a8824d20abedc154a8824d20abeecc54a8824d20eb6d5254e8824d20eb79109568824d20eb79309568824d20eb76119568824d20eb6d219568824d20e37d919568824d20eb5e339568824d20e3f6116568824d20e37d516568824d20a3fdc16568824d20e3de336568824d20a3fdc36568824d20a3fecc6568824d20e3ed815499824d20a7eecc5499824d20e76d5254d9824d20e37d819559824d20e75e339559824d20c7de336d59824d2087fdc36d59824d2087fecc6d59824d20c7ed52aed9824d20c77e55aed9824d2087fdc5aed9824d20c3fdc8aed9824d20a3fdc8aed9824d20a3fcc86559824d208fedc2aed9824d20c3fc98aed9824d2087fdc9aed9824d20c7f4b88469924d20e7f1105469924d2087fccb6069924d20e7e91054a9924d20e7e93054a9924d20e7e61154a9924d20e76d5154a9924d20a7edc154a9924d20a7eecc54a9924d20e76d5254e9924d2087fdcb54e9924d20e779109569924d20e779309569924d20e776119569924d20e76d219569924d20e75e339569924d20c77cb89569924d2087fccb6169924d2087fdcb6169924d20e3f611a229924d20e3ed21a229924d20e3ed52a229924d20e37e55a229924d20b5f4c76d59124520ede9a75c14224520bfe2cc4415224520bfe1c12c15224520afe9ca2c15224520f7e2006455224520f7e1306455224520b7e6cc6455224520fde1102dd5224520f5e5912dd5224520cdedba2dd5224520adedca2dd5224520b7e5c12e55224520dfe110aed5224520cfe9a0aed5224520d7e591aed5224520cdeda7aed52245208fedcaaed5224520ede5a74855224520d7f1106e55224520d7e5216e55224520c5fda76e55224520d3f5816e5822452097f5c16e58224520ede5a74845324520dfe1106c85324520cfe9a06c85324520d7e5916c85324520cfada46c85324520cdeda76c85324520d7e5216e45324520c7eda26e45324520)) else (if i<16 then 0xe5fcc7655a824d20c7fccb655a824d20a7fecc655a824d208ffccb655a824d20cff9106d5a824d20cff9706d5a824d208ffdc06d5a824d20cfed216d5a824d20c7fc916d5a824d20c7fd916d5a824d208ffdc16d5a824d208ffdc26d5a824d208ffdc66d5a824d208ffdc76d5a824d208ffdc96d5a824d208ffecc6d5a824d20c7fdb96d5a824d20a7fdc96d5a824d20cdfdb75d9a824d208ffdcb5d9a824d20e7f910659a824d20c7fdb0659a824d20e7ed21659a824d20e6fd61659a824d20e7f4c1659a824d20a7fdc1659a824d20e7ed52659a824d20e6fd65659a824d20e3fd85659a824d20c7fcb5659a824d20c7fdb5659a824d20a7fcc5659a824d20a7fdc5659a824d20c7fdb7659a824d20a7fecc659a824d20cff9706d9a824d20cfed526d9a824d20c7fc956d9a824d20c7fd956d9a824d208ffcc56d9a824d20e5fd7165da824d20a7fdc165da824d20e7ed5265da824d20e3fd8565da824d20c7fdb565da824d20a7fdc565da824d20c7fdb665da824d20a7fdc665da824d20c7fdb96dda824d20a7fdc96dda824d20cff910aeda824d20cff970aeda824d20cfed21aeda824d20c7fc91aeda824d20c7fd91aeda824d20cfed52aeda824d20c7fd95aeda824d208ffcc5aeda824d20c7fd96aeda824d20c7fd97aeda824d20e5fda79569924d2097fccb9569924d20b7f9c02169924d20b7f5c12169924d20b7edc22169924d20b7ddc32169924d20b7bdc42169924d20b6fdc62169924d20e5fda72169924d20b5fdc72169924d20a7fdca2169924d20e7f9a06169924d2097fccb6169924d20e77d856969924d20c7fcb86969924d20a7fcc86969924d20a7fecc6969924d20e7f9a061a9924d20e6fe5569a9924d20e6fc8569a9924d20e6fd8569a9924d20e6fdc569a9924d20e6fdc869a9924d20e6fd6569a9924d20a7fdc569a9924d20e6fd8669a9924d20e5fd6569e9924d20e5fd8569e9924d20e5fd8669e9924d20e7f9a0a229924d20e6fda6a229924d20e5fda7a229924d2097fccba229924d20e3fd856a29924d20c7fcb56a29924d20a7fcc56a29924d20a7fdc56a29924d20a7fdc66a29924d20a7fecc6a29924d20c7fe556ea9924d20c7fd656ea9924d20c7fc856ea9924d20c7fd856ea9924d20c7fd866ea9924d20c7fe886ea9924d20aff2cc4415124d208efdc6aed8124d20a5fcc76d59124d2087fcc8aed9124d20afe8cb4415224d20afeacc4415224d20afe8cb4c15224d20efe1308455224d20ef65516055224d20cfe910aed5224d20cfe930aed5224d20cfe611aed5224d20cf6d51aed5224d20cf6cb95495324d20af6ecc5495324d20af7acc4425524d20af7acc4c25524d20ef71308465524d20e774988465524d20ef69304865524d20af6ecc4865524d20a77cc86465524d20a77ecc6465524d20 else (if i<17 then 0x97fccb6568824d20cf7cb56968824d20c7fcb96968824d208ffccb6968824d20eef97069a8824d20eeed5269a8824d20e6fd9569a8824d20cefcb569a8824d20e6fda665e8824d20e5fda765e8824d20edf91069e8824d20eded2169e8824d20e5fc9169e8824d20e5fd9169e8824d20eded5269e8824d20e5fd9569e8824d2097fccb5419824d20e6fda65819824d2097fccb5459824d20e7f5516859824d20e7f5816859824d20c7fcb56859824d20e6fda65959824d2097fccb5959824d20e77d516959824d20a7fdc16959824d20a7fdc66959824d20e6fda65d99824d20e5fda75d99824d20a7fdca5d99824d20e6fd506999824d20e6fdc06999824d20e6fd516999824d20e6fd756999824d20e6fdc56999824d20e6fdc76999824d20c7fcb56999824d20e5fd5069d9824d20e5fd6069d9824d20e5fd5169d9824d20e5fd6569d9824d2097fdc0aed9824d208ffccb6959824d20cefcb56999824d20cdfcb569d9824d20cff8b5441a824d20cff9b6441a824d20cff9b7441a824d20cff9b0541a824d20c7fdb9541a824d208ffccb541a824d20cff9b0581a824d208ffdcb581a824d20c7fdb96c1a824d20efe970485a824d20cfecb5485a824d20cfedb6485a824d20cfedb7485a824d20eff110545a824d20c7fdb9545a824d208ffccb545a824d20edf9705c5a824d20aff9c05c5a824d20efe5215c5a824d20cdfdb75c5a824d20e3fd98605a824d20e7f581245a824d20c7fcb5245a824d20a7fdc5245a824d20a7fdc8245a824d20a7fdcb245a824d20c7fcb5645a824d20c7fdb6645a824d20c7fdb7645a824d208ffcc56c5a824d20e7f4916c5a824d20aefcc66c5a824d20c7fdb96c5a824d20a7fdc96c5a824d20efe910549a824d20efe970549a824d20cfedb0549a824d20ef6d51549a824d20ebed81549a824d20e7ec91549a824d20cfedb1549a824d20afedc1549a824d20cfedb5549a824d20cfedb7549a824d20edecc7549a824d20e7edb9549a824d20e7ecc9549a824d20cfeccb549a824d20a7fdc9549a824d20afecc2955a824d20abfcc8955a824d20c7fdb9955a824d20a7fcc9955a824d208ffccb955a824d20cefdb6595a824d20a7fcc9595a824d208ffccb595a824d20edf9705d5a824d20ef6d525d5a824d20cdfdb75d5a824d20c7fdb95d5a824d20ebf910615a824d20ebf970615a824d20cbfdb0615a824d20ebed21615a824d20e3fc91615a824d20e3fd91615a824d20abfdc1615a824d20ebed52615a824d20abfdc2615a824d20eb7d65615a824d20cbfdb7615a824d20e3fdc9615a824d20e3fd98615a824d20e7f970655a824d20c7fdb0655a824d20e77d51655a824d20e3fd81655a824d20c7fdb1655a824d20a7fdc1655a824d20e3fd85655a824d20c7fdb5655a824d20c7fdb7655a824d20 else 0xadfdc76858724d20a7fdc96858724d20fd6d525d58724d2097fccb6558724d20ef6d526958724d20eb7d856958724d208ffccb6958724d20ecfda65d98724d20b7f4c16598724d20e5fda76598724d2097fccb6598724d20eef9106998724d20eeed216998724d20ecfd716998724d20e6fd916998724d20eeed526998724d20ecfd756998724d20eafd856998724d20e6fd956998724d20cefdb56998724d20ecfdc76998724d20e6fd986998724d20e6fdc96998724d20cefccb6998724d20cefdcb6998724d20c7fdb96998724d208ffccb6998724d20cefda66d98724d20cefda6aed8724d2097fdc9aed8724d208ffdcaaed8724d2097fcc86c59724d20e77d516959724d20a7fdc16959724d20e77d856959724d20a7fcc86959724d20a7fecc6959724d2097fcc86d59724d20e5fda76199724d20e6fd856999724d20e6fdc56999724d20e6fdc86999724d20e6fd656999724d20a7fdc56999724d20e6fd866999724d2097fcc86d99724d20adfcc8541a724d20adfecc541a724d20edf950601a724d20edf960601a724d20adfcc5601a724d20e5fdc9601a724d20adfecc601a724d20edee55485a724d20edec85485a724d20adfcc8545a724d20e5fd98605a724d20e5fe55245a724d20e5fc85245a724d20e5fe55645a724d20e5fc85645a724d20eded60549a724d20eded80549a724d20eded81549a724d20edf910595a724d20ecfd60595a724d20adfdc0595a724d20eded21595a724d20e5fd91595a724d20e5fcc9595a724d20e5fdc9595a724d20adfecc595a724d20edf910615a724d20e9fd80615a724d20adfdc0615a724d20eded21615a724d20e5fc91615a724d20e5fd91615a724d20adfdc1615a724d20ed7d65615a724d20e5fd98615a724d20e5fdc9615a724d20adfdc9615a724d20adfecc615a724d20e5fd60655a724d20e5fd80655a724d20e5fd81655a724d20e5fcc8655a724d20adfcc8655a724d20edf910619a724d20adfdc0619a724d20eded21619a724d20e5fd91619a724d20eded52619a724d20edecb2619a724d20ecfd65619a724d20e5fd95619a724d20adfdc5619a724d20e5fd50659a724d20e5fd80659a724d20e5fd85659a724d20ecfd65659a724d20a7fdc9619a724d20a7fcc8659a724d20eef9a64428824d20edf9a75c28824d20efe9a04868824d20eeeda64868824d20e7f9a02468824d20b7edc22468824d20b7ddc32468824d20b7bdc42468824d20b77dc52468824d20b6fdc62468824d20b5fdc72468824d20b3fdc82468824d20e7f9a06468824d20e6fda66468824d20aff9c06868824d20efe5216868824d20e7f4916868824d20a7fcc96868824d20a7fdc96868824d20efe9a054a8824d20ef6da554a8824d20d7ecb954a8824d20e7f9a06568824d20b5fcc76568824d20))) else (if i<21 then (if i<19 then 0xc7fdb76959624d20a7fdc76959624d20c7fcb86959624d20c7fdb86959624d20a7fcc86959624d20c7fccb6959624d20a7fecc6959624d20c7fda56d59624d2097fcc86d59624d20c7fda5aed9624d20aefdc66959624d20aefcc8541a624d20aefdcb541a624d20aefecc541a624d20eef950601a624d20eef9b0601a624d20aefcc5601a624d20e6fdb9601a624d20e6fdc9601a624d20aefdcb601a624d20aefecc601a624d20eeec85485a624d20aefcc8545a624d20e6fc85645a624d20eeed50549a624d20eeed80549a624d20eeedb0549a624d20eeed51549a624d20eeed81549a624d20eeecc8549a624d20aefcc8549a624d20eef910955a624d20eeed21955a624d20e6fc91955a624d20e6fd91955a624d20e6fc98955a624d20e6fd98955a624d20aefcc8955a624d20aefccb955a624d20eef9105d5a624d20eeed215d5a624d20e6fd915d5a624d20aefdcb5d5a624d20aefdc0215a624d20aefdc9215a624d20eef910615a624d20eef970615a624d20eafd80615a624d20aefdc0615a624d20eeed21615a624d20e6fd91615a624d20aefdc1615a624d20eeed52615a624d20aefdc2615a624d20e6fd98615a624d20e6fdc9615a624d20aefdc9615a624d20aefccb615a624d20aefecc615a624d20e6fd50655a624d20e6fd80655a624d20e6fdb0655a624d20e6fd51655a624d20e6fd81655a624d20e6fd85655a624d20e6fcc8655a624d20aefcc8655a624d20aefdc82d5a624d20eef9706d5a624d20eeed526d5a624d20e6fd956d5a624d20eeed526dda624d20e6fd956dda624d20eef9702e1a624d20aefdc52e1a624d20aefdc72e1a624d20eef9706e1a624d20eeed526e1a624d20e6fc956e1a624d20e6fd956e1a624d20aefcc56e1a624d20e6fe552e5a624d20e6fd852e5a624d20eef970aeda624d20e6fd96541a624d20aefdc6541a624d20a7fdc9541a624d20cff8b85c1a624d20efe970485a624d20eeed60549a624d20efe970549a624d20cfedb5549a624d20cfedb7549a624d20afecc2955a624d20e6fd96955a624d20a7fcc9955a624d208ffccb955a624d20eef970595a624d20eeed52595a624d20edf9705d5a624d20ef6d525d5a624d20e6fd965d5a624d20aefdc65d5a624d20a7fdc95d5a624d208ffdcb5d5a624d20a7fcc9615a624d20a7fdc9615a624d208ffccb615a624d20e6fd60655a624d20e7f970655a624d20e6fd65655a624d20c7fdb5655a624d20c7fdb7655a624d20a7fcc8655a624d20cff9706d5a624d20eeed525d9a624d20e6fd955d9a624d20eef970619a624d20eeed52619a624d20e6fc95619a624d20e6fd95619a624d20cff970aeda624d20edf9a74418724d20ededa74858724d20fde5215c58724d20e5fda76458724d20aff9c06858724d20efe5216858724d20 else (if i<20 then 0xefe5215c5a524d20aefcc6605a524d20e3fd98605a524d20c7fdb9605a524d208ffccb605a524d20e7f581245a524d20a7fdc5245a524d20c7fcb8245a524d20a7fdc8245a524d20a7fdcb245a524d20c7fdb6645a524d20c7fcb7645a524d20c7fdb7645a524d20a7fdc7645a524d20c7fcb8645a524d20a7fdc8645a524d20a7fdcb645a524d208ffcc86c5a524d20ef6d81549a524d20efe910549a524d20cefdb6589a524d20a7fdc9609a524d208ffcc86c9a524d20a7fcc9595a524d20ef7910615a524d20ef7970615a524d20eb7d80615a524d20ef6d21615a524d20e77c91615a524d20e77d91615a524d20af7dc1615a524d20af7dc2615a524d20cf7db6615a524d20e77d98615a524d20c7fcb96d9a524d20a7fcc96d9a524d20aff9c02e1a524d20aff5c12e1a524d20afedc22e1a524d20afddc32e1a524d20afbdc42e1a524d20aefdc62e1a524d20adfdc72e1a524d20a7fdc92e1a524d20cff910aeda524d20cff970aeda524d208ffdc0aeda524d20cfed21aeda524d20c7fc91aeda524d20c7fd91aeda524d208ffdc1aeda524d208ffdc2aeda524d208ffdc6aeda524d208ffdc7aeda524d20c7fd98aeda524d208ffcc8aeda524d208ffdc8aeda524d20eef9a64417624d20edf9a74417624d20cff9ba4417624d20eeeda64857624d20ededa74857624d20cfedba4857624d20e6fda66457624d20e5fda76457624d20c7fdba6457624d20efe5216857624d20ef6d526957624d20aefdc66957624d20eef9a64418624d20edf9a75c18624d20cefda66c18624d20efe9a04858624d20eeeda64858624d20e7f9a06458624d20e6fda66458624d20aff9c06858624d20efe5216858624d20efe9a05498624d20ef6da55498624d20b7ecc95498624d20eef9a05958624d20e7f9a06558624d20b5fcc76558624d20aefdc66958624d20a7fcc96958624d20cff9a06d58624d20cefda66d58624d2097fcc96d58624d2097fdcb5419624d20d7f4752c59624d20d7f4852c59624d20d7f6772c59624d20d7f4872c59624d20d7f6882c59624d2097fcc56c59624d2097fcc86c59624d20d7f4b19559624d20b7ecc29559624d20e5fda79559624d2097fccb9559624d20f6f9105959624d20f6ed215959624d20e6fda15959624d20f6f4b15959624d20f6ed525959624d20e6fda25959624d20e6fda75959624d20d6fdb75959624d20d6fdb85959624d20b6fcc85959624d20d6fccb5959624d20d7f4b15d59624d20e5fda75d59624d20e7f9a06159624d20d7f4b16159624d20f67d656159624d20e6fda66159624d2097fccb6159624d2097fdcb6159624d20e7f9106959624d20e7ed216959624d20e6fd616959624d20e7f4b16959624d20c7fdb16959624d20e6fd656959624d20e77d856959624d20e6fdc66959624d20 else 0x97fdc9aed6524d20edf9a74417524d20fde9704857524d20ededa74857524d20e5fda76457524d20edf9706857524d20efe5216857524d20dff1b14408524d20dfe9b24408524d20dfb9b44408524d20eef9a64408524d20edf9a74408524d20d7f9b94408524d209ff9c16c08524d20cdfda76c08524d20dfe9b04848524d20dfe5b14848524d20dfadb44848524d20d7edb94848524d209fedcb4848524d20d7f9b02448524d20d7f5b12448524d20d7edb22448524d20b7edc22448524d20b7ddc32448524d20d7bdb42448524d20b7bdc42448524d20b77dc52448524d20b6fdc62448524d20b5fdc72448524d20b3fdc82448524d2097fdcb2448524d20d7f9b06448524d20d7f5b16448524d20d7edb26448524d20d7bdb46448524d2097fdcb6448524d20cff9b06848524d20efe5216848524d20e7f4916848524d20cff5b16848524d20cfedb26848524d20cfbdb46848524d20c7fdb96848524d20a7fcc96848524d20dfd9106cc8524d20dfcd216cc8524d20d7dc916cc8524d20d7dd916cc8524d20cfdda16cc8524d20def9106d88524d20deed216d88524d20d6fc916d88524d20d6fd916d88524d20cefda16d88524d20ddf9106dc8524d20dded216dc8524d20d5fc916dc8524d20d5fd916dc8524d20cdfda16dc8524d20cff9106e88524d20cfed216e88524d20c7fc916e88524d20c7fd916e88524d208ffdc16e88524d20efe9a04858524d20e7f9a02458524d20b7f9c02458524d20b7edc22458524d20b7ddc32458524d20b7bdc42458524d20b77dc52458524d20e6fda62458524d20b6fdc62458524d20b5fdc72458524d20b3fdc82458524d2097fdcb2458524d20e7f9a06458524d2097fdcb6458524d20aff9c06858524d20efe5216858524d20e7f4916858524d20cff5b16858524d20c7fdb96858524d20a7fcc96858524d20a7fdc96858524d20efe9a05498524d20ef6da55498524d20ededa75498524d20ef79a05958524d20ee7da65958524d20cff9a0aed8524d2097fcc9aed8524d208ffdcaaed8524d20e5fda75419524d2097fccb6019524d20e77da55459524d20e5fda75459524d20e7f9a06059524d2097fccb6059524d20e7f5516859524d20e7f5816859524d20a7fdc56859524d20c7fcb86859524d2097fcc86c59524d20e5fda75959524d20e7f9a06159524d20e77da56159524d20e5fda76159524d2097fdcb6159524d20e7f9a02e19524d2097fdc0aed9524d20c7fda5aed9524d2097fdc8aed9524d20cff9b6441a524d20cff9b7441a524d20aff9c7441a524d20cff8b8441a524d20cefdb6581a524d20cff8b85c1a524d208ffccb601a524d208ffcc86c1a524d20efe970485a524d20afedc5485a524d20cfedb6485a524d20cfedb7485a524d20cfecb8485a524d20eff110545a524d20)) else (if i<23 then (if i<22 then 0xc7fdb764da526120a7fdc764da526120a7fccb64da526120a7fdcb64da526120a7fecc64da526120cfed216cda526120c7fc916cda526120c7fd916cda5261208ffdc16cda526120cfed426cda5261208ffdc26cda5261208ffdc76cda5261208ffdc96cda5261208ffecc6cda526120efad42551a526120efad425d1a526120a7fcc36e5a526120cff910aeda526120cff930aeda526120cff970aeda526120cfed21aeda526120c7fc91aeda526120c7fd91aeda526120cfed42aeda526120c7fd93aeda5261208ffcc3aeda52612097fcc36c59726120f76d515499726120e7eda15499726120e7bda450d9726120f76d5254d9726120e5fda15cd9726120e5fda45cd9726120e5fd7168d9726120c7fdb168d9726120e7ed5268d9726120e7dd5368d9726120e5fd7368d9726120c7fdb468d9726120a7fdc468d9726120a7fecc68d9726120c7fda16cd9726120e7bda45519726120c7fda16d19726120e77d536959726120a7fcc36959726120a7fdc36959726120a7fdc46959726120a7fecc6959726120c7fda16d59726120c7fda36d5972612097fcc36d59726120efe930485a726120efe910509a726120efe930509a726120efad4250da726120e7ed4264da726120e7f930651a726120a7fdc3651a726120c7fdba54e992612097fccb54e9926120c7fdba956992612097fccb9569926120e77d536969926120c7fcb36969926120a7fdc36969926120a7fecc69699261209ff8cb5418024d20eef9a65818024d209fedc2aed8024d2097fdc9aed8024d208ffdcaaed8024d20d77cc86d49124d20d77dc86d49124d20d77ecc6d49124d20d7f5816d49124d2097fcc86d49124d20c7fdca6d49124d2097fecc6d49124d20d3fcc56e09124d20d3fdc56e09124d20d3fecc6e09124d20ef6da55415224d20ededa75415224d20ef6da55815224d20ef6da56015224d20bf6cc56015224d20b7edc96015224d20ffe1105455224d20ef6da55455224d20ededa75455224d20efe9a06055224d20f7e5812455224d20b7edc82455224d20efe5516855224d20efe5816855224d20afedc56855224d20bfcdc32e15224d20ef6da52e15224d20afedca2e15224d2097fcc86e55224d20edf9a74425524d20b7f9c02465524d20b7edc22465524d20b7ddc32465524d20b7bdc42465524d20b77dc52465524d20b6fdc62465524d20b5fdc72465524d20b3fdc82465524d20efe5216865524d20e7f4916865524d20eef9a64416524d20eeeda64856524d20e6fda66456524d20efe5216856524d20ef6da55496524d20ededa75496524d20d7ecb95496524d20ecfda75896524d20aefdca5896524d20e6fda62e56524d20c7fdba2e56524d20a7fdca2e56524d20b7f4c16e56524d20b5fcc76e56524d20cefda6aed6524d2097fcc9aed6524d20 else 0xcfedba4857426120c7fdba6457426120a7fdc96857426120ffa9105097426120efada15097426120bfadc45497426120b7f8c94425526120dfe8b24c25526120dfd8b34c25526120b7ecc94865526120e7f4916865526120a7fcc96865526120edf9a74417526120edf9a74c17526120fde9704857526120ededa74857526120e5fda76457526120edf9706857526120fde9705097526120dfadb45097526120ededa75097526120ff69105497526120ff69305497526120ef6da1549752612097fccb4c59526120e7bda4505952612097fccb505952612097fccb5c59526120e7f9706859526120e7f5316859526120e7f5516859526120c7fcb36859526120a7fdc46859526120a7fdc56859526120a7fdc7685952612097fcc36c59526120d5fcb78cd952612097fccb8cd9526120e7bda450d9526120d5fcb750d952612097fccb5cd9526120a7fdca2cd9526120c7fda16cd9526120c7fda1aed952612097fdc1aed952612097fdc2aed952612097fdc3aed9526120c7fda7aed952612097fdc7aed952612097fdcb64d95261209ff9c0aed95261209fedc2aed952612097fdc9aed95261208ffdcaaed9526120cff8b3441a526120cff9b4441a526120cff9b7441a526120aff9c7441a526120cff9b24c1a526120cff9b44c1a526120efb8c44c1a526120cff9b74c1a526120aff9c74c1a526120e7f8c94c1a526120cff8b35c1a526120cff9b45c1a526120efe930485a526120efe970485a526120cfecb3485a526120cfedb4485a526120afedc5485a526120cfedb7485a526120efd9304c5a526120aff9c04c5a526120efe5214c5a526120c7fdb94c5a5261208ffccb4c5a526120eff110505a526120ef7930545a526120eff110545a526120efe5215c5a526120c7fcb3645a526120c7fdb4645a526120c7fdb7645a526120a7fdc7645a526120a7fdcb645a526120cff9306c5a5261208ffcc36c5a526120cfedb24c9a526120c7fdb94c9a526120a7fdc94c9a526120efe910509a526120efe930509a526120efe970509a526120efad41509a526120afedc1509a526120cfedb7509a526120efe910549a526120efe930549a526120aff8c08cda526120af7cc58cda526120c7fdb98cda526120a7fcc98cda5261208ffccb8cda526120efd93050da526120efad4250da526120c7fdb950da526120ef791054da526120ef5d3054da526120ef797054da526120ef6d2154da526120e77c9154da526120e77d9154da526120af7dc154da526120ef6d4254da526120cf7db254da526120cf7db454da526120efd93054da526120ef5d535cda5261208ffccb5cda526120e7dd3164da526120e77d5164da526120c7fdb164da526120a7fdc164da526120e7ed4264da526120c7fdb264da526120c7fdb464da526120e7bcc464da526120) else (if i<24 then 0xabfdc461da824520e9fd7561da824520e3fd9561da824520cbfdb561da824520abfdc561da824520abfecc61da824520e3fd9861da824520e7f93065da824520e7ed5265da824520e5fd7365da824520e3fd8365da824520c7fdb365da824520a7fdc365da824520e3fd8465da824520c7fdb465da824520a7fdc465da824520e3fd8565da824520c7fdb565da824520a7fdc565da824520c7fdb96dda824520a7fdc96dda824520ebed42a21a824520ebed52a21a824520e3fd95a21a824520abfcc5a21a824520e3fd97a21a824520e3fd53661a824520e3fd74661a824520e3fdb5661a824520e3fdb7661a824520e3febb661a824520cfed42aeda824520cfed52aeda824520c7fc95aeda824520c7fd95aeda8245208ffcc5aeda824520c7fd97aeda824520d7f4b56069924520d7f4b86069924520e7eda254e9924520e7f9a06169924520e7eda26169924520e77d836969924520e77dc36969924520e77dc86969924520e7f5816969924520e77d536969924520a7fdc36969924520e77d856969924520e6fd5369a9924520e6fd8569a9924520e5fd5369e9924520e5fd8369e9924520e5fd8569e9924520e7eda2a229924520e77da5a229924520e6fda6a229924520e5fda7a22992452097fccba229924520e3fd536a29924520e3fdc56a29924520e3fecc6a29924520e3fd856a29924520c7fcb56a29924520a7fdc56a29924520e3fe886a29924520c7fccb6a29924520a7fecc6a29924520c7fd536ea9924520c7fd856ea9924520c7fe886ea9924520efe9706854226120ffe1514415226120efe9a74415226120bfe9c74415226120ff69534c15226120efe9a74c15226120bfe9c74c15226120ffe1105055226120efada45055226120ff69305455226120efe9306855226120efe9706855226120efe5316855226120efe5516855226120afedc46855226120afedc56855226120afedc76855226120dfe9306c55226120bfe9c02cd5226120afedca2cd5226120fde9302dd5226120dfe5b14845326120d7f5b16445326120cff5b16845326120dfe9106c85326120cfeda16c853261209fedc16c85326120c7fda16e4532612097fdc16e45326120cfed216e85326120c7fd916e853261208ffdc16e85326120b7ecc9485532612097fdcb6455326120e7f4916855326120cff5b16855326120a7fcc96855326120a7fdc96855326120ff69105495326120ff69705495326120ef6da15495326120ff4d735495326120ef6da754953261208ffdcaaed5326120efb9a44415426120efb9a45c15426120efada44855426120e7bda46455426120ffa9105095426120ffa9705095426120efada15095426120efada75095426120dfe9106c95426120dfe9706c95426120cfeda16c95426120cfeda76c954261209ff9c0aed5426120 else 0xebf9306d5a824520ebf9706d5a824520ebed426d5a824520ebed526d5a824520abfdc26d5a824520eb7d536d5a824520e3fd936d5a824520abfcc36d5a824520abfdc36d5a824520e3fd956d5a824520e3fcc96d5a824520e3fdc96d5a824520abfecc6d5a824520e3fd5365da824520e3fdb365da824520e3fdb565da824520ebf9306dda824520ebed426dda824520ebed526dda824520e9fd736dda824520e3fd936dda824520abfdc36dda824520e3fd946dda824520abfdc46dda824520e9fd756dda824520e3fd956dda824520cbfdb56dda824520abfdc56dda824520abfecc6dda824520ebed42aeda824520ebed52aeda824520e3fd95aeda824520abfcc5aeda824520e3fd97aeda824520efe970509a824520cfedb7509a824520efe930549a824520efe970549a824520cfedb4549a824520cfedb5549a824520cfedb7549a824520edecc7549a824520ebecc8549a824520e7edb9549a824520e7ecc9549a824520cfeccb549a824520abfcc8549a824520a7fdc9549a8245208ffccb549a824520abfcc5609a8245208ffcc56c9a824520afedc214da824520abfdc814da824520a7fdc914da8245208ffdcb14da824520ef6d5254da824520e3fc9854da824520abfcc854da824520a7fcc954da8245208ffccb54da824520efad42551a824520afedc2551a824520cfbdb4551a824520efad425d1a824520c7fdb95d1a8245208ffdcb5d1a824520afecc2955a824520e3fc98955a824520abfcc8955a824520a7fcc9955a8245208ffccb955a824520edf9705d5a824520ef6d525d5a824520cdfdb75d5a824520abfdc2215a824520abfdc3215a824520ebf930615a824520ebf970615a824520ebed42615a824520ebed52615a824520abfdc2615a824520eb7d53615a824520abfcc3615a824520abfdc3615a824520cbfdb7615a824520e3fcc9615a824520e3fdc9615a824520abfecc615a824520e3fd98615a824520a7fcc9615a824520e7f970655a824520e7ed42655a824520e3fd83655a824520a7fcc3655a824520a7fdc3655a824520c7fdb4655a824520e3fd85655a824520c7fdb5655a824520c7fdb7655a824520e5fcc7655a824520e3fcc8655a824520a7fcc8655a824520c7fccb655a824520a7fccb655a824520a7fecc655a824520abfcc8655a8245208ffccb655a824520cff9306d5a824520cff9706d5a824520cfed426d5a8245208ffdc26d5a824520cf7d536d5a824520c7fd936d5a8245208ffcc36d5a8245208ffdc36d5a8245208ffdc46d5a8245208ffdc76d5a824520c7fcc96d5a8245208ffecc6d5a824520c7fdb96d5a824520a7fcc96d5a824520a7fdc96d5a824520ebf93061da824520ebed4261da824520ebed5261da824520e9fd7361da824520e3fd9361da824520abfdc361da824520))))) else (if i<38 then (if i<31 then (if i<28 then (if i<26 then 0xefd93050da724520efe52160da724520a7fcc864da724520efe521611a724520a7fdc9611a724520ffe1304868824520ffe1704868824520f7e5934868824520efe5a34868824520dfe4b34868824520dfe4b54868824520efd5a34868824520efe9a050a8824520efada450a8824520efe9a054a8824520ef6da554a8824520d7ecb954a8824520afedca54a8824520e7f9a06568824520f7e5216568824520e7eda26568824520e77da56568824520b5fcc7656882452097fccb6568824520ef79306968824520ef79706968824520ef6d426968824520e77d936968824520cf7cb36968824520e77cc96968824520cf7ccb6968824520cf7cb56968824520c7fcb969688245208ffccb6968824520eeed4269a8824520eeed5269a8824520e6fd9569a8824520cefcb569a8824520e7eda265e8824520e7dda365e8824520e77da565e8824520e6fda665e8824520e5fda765e8824520edf93069e8824520edf52169e8824520eded4269e8824520eded5269e8824520e5fd9369e8824520cdfcb369e8824520e5fd9469e8824520e5fd9569e8824520efe52169e8824520d7f4b54859824520f3f5736059824520f3f5756059824520d7f4b56059824520d7f4b76059824520f7e5815499824520f3f58154d9824520e7eda254d982452097fccb54d9824520f3f5815d19824520e5fda75d19824520a7fdca5d19824520e7f9a06159824520f3f5816159824520e7eda2615982452097fccb6159824520e77d836959824520e77dc36959824520e77d746959824520e77e886959824520e77dc86959824520e7f5816959824520e77d536959824520c7fcb36959824520a7fdc36959824520e77d856959824520d7f5816d59824520e6fd536999824520e6fd746999824520e6fd856999824520e6fe886999824520f3f58161d9824520e7eda261d9824520e7dda361d9824520e77da561d9824520e6fda661d9824520e5fda761d9824520e5fd5369d9824520e5fd8369d9824520e5fd8469d9824520e5fd8569d9824520e5fe8869d9824520d7f5816dd9824520d7f581aed9824520c7fda8aed9824520ef75816959824520eef5816999824520ebed73509a824520ebeccb549a824520abfccb549a824520abfcc56c9a824520abfdcb14da824520ebed4254da824520ebed5254da824520e3fcb954da824520e3fcc954da824520e3fdc954da824520abfccb54da824520abfecc54da824520eb7d53551a824520ebed525d1a824520ebbd545d1a824520abfcc3955a824520e3fcb9955a824520abfccb955a824520ebed425d5a824520abfdc35d5a824520abfdc45d5a824520e3fd53655a824520e3fd73655a824520e3fd74655a824520e3fd75655a824520e3fccb655a824520abfccb655a824520abfdc22d5a824520abfdc32d5a824520 else (if i<27 then 0xed7dc76958724520eb7dc86958724520cf7dcb6958724520ef6d526958724520afedc26958724520ed7d756958724520eb7d856958724520e77d956958724520dfe5216d58724520cfeda26d58724520cfdda36d58724520cf7da56d58724520eef9306998724520eef5816998724520eeed426998724520eeed526998724520ecfd736998724520e6fd936998724520cefdb36998724520cefdb46998724520ecfd756998724520eafd856998724520e6fd956998724520cefdb56998724520dfe521aed8724520cfeda2aed8724520cfdda3aed8724520cf7da5aed8724520cefda6aed872452097fdc9aed87245208ffdcaaed8724520f7f1306059724520f7e5815499724520e7eda254d9724520f5f5815cd9724520e7eda260d9724520e5fda760d9724520e7ddc568d9724520e7ddc868d9724520e7f58168d9724520e7dd5368d9724520e7dd8368d9724520d7f5816cd972452097fcc86cd9724520e7dda36119724520e7bda46119724520e5fda76119724520d7f5816d1972452097fcc86d19724520e7eda26159724520e7dda36159724520e77d836959724520e77dc36959724520e77d846959724520e77dc86959724520e7f5816959724520e77d536959724520a7fdc36959724520e77d856959724520d7f5816d5972452097fcc86d59724520e6fd536999724520e6fd836999724520e6fd846999724520e6fd856999724520edf8b84c1a724520adfcc58cda724520adfcc88cda724520edf9b050da724520adfdcb50da724520edf93054da724520eded4254da724520e5fc9854da724520adfcc854da724520e5fcc954da724520e5fdc954da724520adfecc54da724520adfdc520da724520edf93060da724520adfdc060da724520edf52160da724520eded4260da724520eded5260da724520eddd5360da724520e5fc9860da724520e5fcc960da724520e5fdc960da724520adfecc60da724520e5fd5364da724520e5fd8364da724520e5fdb364da724520e5fdb464da724520e5fdb564da724520e5fcb864da724520e5fdb864da724520e5febb64da724520ed7d53551a724520adfdc3551a724520edf930611a724520eded52611a724520edbd43611a724520e9fd83611a724520e5fd93611a724520adfdc3611a724520edbd54611a724520adfecc611a724520e5fd53651a724520e5fd83651a724520e5fdb3651a724520e5fdb5651a724520e5fcb8651a724520e5fdb8651a724520e5febb651a724520edf930615a724520eded42615a724520ed7d53615a724520e5fd93615a724520adfcc3615a724520adfdc3615a724520e5fd94615a724520adfdc4615a724520e5fcc9615a724520e5fdc9615a724520adfecc615a724520e5fd83655a724520e5fd84655a724520e5fcc8655a724520adfcc8655a724520 else 0xaf7cc8955a524520ef75815d5a524520ef6d425d5a524520af7dc35d5a524520af7dc45d5a524520af7dc2215a524520af7dc3215a524520ef7930615a524520ef7970615a524520ef7581615a524520ef6d42615a524520af7dc2615a524520e77d93615a524520cf7db3615a524520af7cc3615a524520af7dc3615a524520e77cc9615a524520af7ecc615a524520a7fcc9615a524520e77d73655a524520e77d83655a524520e77d74655a524520e77cc8655a524520ef7581655a524520af7cc8655a524520a7fcc96e1a524520a7fcc36e5a5245208ffcc3aeda5245208ffcc8aeda524520eef5814c9a624520eeed73509a624520eeecc8549a624520eef581549a624520aefcc8549a624520eef581609a624520aefcc5609a624520eef58114da624520aefdc814da624520eef58154da624520eeed4254da624520eeed5254da624520e6fc9854da624520aefcc854da624520e6fcc954da624520e6fdc954da624520aefecc54da624520eef581551a624520ee7d53551a624520eef5815d1a624520eeed525d1a624520eebd545d1a624520eef581955a624520aefcc3955a624520e6fc98955a624520aefcc8955a624520eef5815d5a624520eeed425d5a624520aefdc35d5a624520aefdc45d5a624520aefdc2215a624520aefdc3215a624520eef930615a624520eef970615a624520eef581615a624520eeed42615a624520eeed52615a624520aefdc2615a624520ee7d53615a624520aefcc3615a624520aefdc3615a624520e6fcc9615a624520e6fdc9615a624520aefecc615a624520e6fd53655a624520e6fd73655a624520e6fd83655a624520e6fd74655a624520e6fd75655a624520e6fd85655a624520e6fcc8655a624520eef581655a624520aefcc8655a624520efe9a24c18724520efd9a34c18724520edf9a74c18724520ffe1304858724520efada45098724520ededa75098724520fde5215cd8724520ededa25cd8724520f7e52164d8724520e7eda264d8724520b7bcc464d8724520e5fda764d872452097fccb64d8724520efd9c068d8724520efd58168d8724520efcd4268d8724520efcd5268d8724520edddc768d8724520e7ddc968d8724520cfddcb68d8724520efe52168d8724520eddd7368d8724520adfdc768d8724520dfe5216cd8724520cfeda26cd8724520cfdda36cd8724520dfe5216d18724520fde5215d58724520fd6d525d58724520ededa25d58724520eddda35d58724520fbe5216158724520ebeda26158724520ebdda36158724520f7e5216558724520e7eda26558724520e7dda3655872452097fccb6558724520ef79306958724520ef75816958724520ef6d426958724520ef6dc26958724520ed7d736958724520e77d936958724520cf7db36958724520cf7db46958724520)) else (if i<29 then 0xef79706cda524520ef75816cda524520ef6d426cda524520ef5d736cda524520ef5d836cda524520e77d936cda524520e77c986cda524520af7cc86cda524520e77cc96cda524520af7ecc6cda524520ef79305d1a524520ef75815d1a524520ef6db25d1a524520ed7d735d1a524520e77d935d1a524520af7dc35d1a524520ef75816d1a524520cf7db36d1a524520af7dc36d1a524520ef3d746d1a524520ef75816dda524520ef6d426dda524520af7dc36dda524520af7dc46dda524520af7dc22e1a524520af7dc32e1a524520ef79306e1a524520ef79706e1a524520ef75816e1a524520ef6d426e1a524520af7dc26e1a524520e77d936e1a524520cf7db36e1a524520af7cc36e1a524520af7dc36e1a524520e77cc96e1a524520af7ecc6e1a524520e77d832e5a524520ef7581aeda524520af7cc3aeda524520af7cc8aeda524520cff9b34c1a524520eff130605a524520ef7550605a524520eff170605a524520efe552605a524520efe5b2605a524520ef7485605a524520ef74c5605a524520e7f498605a524520e7f5b9605a524520e7f4c9605a524520e7f5c9605a524520cff4cb605a524520a7fdc94c9a524520efe581509a524520cfedb7509a524520ef6cc8549a524520ef7581549a524520af7cc8549a524520ebf581609a524520af7cc5609a524520a7fdc9609a5245208ffccb609a524520cfed736c9a524520cfee776c9a524520cfec876c9a524520cfecc76c9a524520cfecc86c9a5245208ffcc86c9a524520aff8c08cda524520af7cc58cda524520a7fcc98cda5245208ffccb8cda524520efad4250da524520ef758114da524520af7dc814da524520ef793054da524520ef797054da524520ef758154da524520ef6d4254da524520cf7db454da524520e77c9854da524520af7cc854da524520e77cc954da524520af7ecc54da524520a7fcc954da524520ef5d535cda524520aff9c020da524520aff5c120da524520afedc220da524520afbdc420da524520af7dc520da524520aefdc620da524520adfdc720da524520a7fdc920da5245208ffdcb20da524520ef6d5260da524520cfedb260da524520ef5d5360da524520af7cc560da524520c7fdb960da524520a7fcc960da524520a7fdc960da5245208ffccb60da524520e7f58164da524520e77d5364da524520c7fdb364da524520a7fcc864da524520cff5816cda524520cfed426cda5245208ffdc76cda524520c7fc986cda5245208ffcc86cda524520c7fcc96cda5245208ffecc6cda524520a7fcc96cda524520ef7581551a524520cf7db3551a524520af7dc3551a524520efad425d1a524520ef6d525d1a524520cfedb25d1a524520ef3d545d1a524520cfbdb45d1a524520ef7581955a524520af7cc3955a524520e77c98955a524520 else (if i<30 then 0xefe9a24c18524520d7f8b94c18524520efe9a25c18524520ffe1304858524520ffe1704858524520f7e5934858524520efe5a34858524520dfe4b34858524520dfe5b44858524520efe5a74858524520dfe5cb4858524520dfe5b24858524520efd5a34858524520edf5a74858524520d7f5b94858524520d7f4b96058524520efe9a05098524520efada45098524520efe9a05498524520ef6da55498524520ededa75498524520afedca5498524520ff593054d8524520ef79a054d8524520ff652154d8524520ef6da254d85245209f7ccb54d8524520dfe5216cd8524520cfeda26cd852452097fcc96cd852452097fdc96cd8524520e7f9a02e58524520b7f5c12e58524520e7eda22e58524520e7f9a06e58524520e7eda26e58524520e77da56e58524520b5fcc76e58524520c7fdba6e58524520c7fcb96e98524520a7fcc96e98524520cff9a0aed8524520dfe521aed8524520cfeda2aed852452097fcc9aed852452097fdc9aed85245208ffdcaaed8524520f7e5734859524520f7e5744859524520f7e5844859524520f7e5754859524520f7e6774859524520f7e4874859524520f7e4b74859524520d7f4b84859524520f7f1706059524520d7f4b36059524520d7f4b86059524520d7f4cb6059524520f7e5815099524520e7f9a054d9524520f7e52154d9524520e7eda254d9524520d7dcb354d9524520e77da554d9524520e5fda754d952452097fccb54d9524520e7f9a060d9524520f7e52160d9524520e7eda260d9524520d5fcb760d952452097fccb60d9524520d7f5816cd952452097fcc86cd9524520e7bda45d19524520e7f9a06159524520f7e5216159524520e7eda26159524520e77da56159524520e5fda7615952452097fccb6159524520f5f5812dd9524520e7f9a02e19524520f7e5212e19524520b7f5c12e19524520e7eda22e19524520e7dda32e19524520e7bda42e19524520d7f581aed952452097fdc8aed9524520dfe4b84859524520ef79734c1a524520ef79b74c1a524520ef7530605a524520ef7580605a524520ef75b0605a524520ef75814c9a524520ef6d73509a524520ef7581609a524520af7ccb609a524520ef6e886c9a524520ef6cc86c9a524520ef75816c9a524520af7cc86c9a524520ef75818cda524520af7cc88cda524520af7ccb8cda524520ef797050da524520ef758150da524520ef75815cda524520af7dcb20da524520ef793060da524520ef797060da524520af7dc060da524520ef758160da524520ef6d4260da524520ef6db260da524520e77cc960da524520e77dc960da524520af7ccb60da524520af7ecc60da524520e77d7364da524520e77d8364da524520e77db764da524520ef758164da524520ef75812cda524520af7dc82cda524520ef79306cda524520 else 0xa7fcc854e9924d20c7fccb54e9924d20c7fdcb54e9924d20a7fecc54e9924d20a7fdc16169924d20e77d536169924d20a7fdc36169924d20c7fccb6169924d20c7fdcb6169924d20a7fecc6169924d20a7fcc86569924d20bfe4c56d12124520bfe4c86d12124520bfe4c86d52124520bfe4c56e12124520efd5a360d2124520b7f4c56e58124520ffe1706054224520ffe1306055224520ffe1706055224520f7e5c96055224520fde5812dd5224520bfe5c12e15224520efcda32e15224520efada42e15224520cfedba2e15224520afedca2e15224520f7e5812e55224520dfe4b84855224520d7f5816e5522452097fcc86e55224520dfe4b54858224520dfe5816c85324520dfe5216e05324520cfeda26e05324520cdfda76e05324520d7f5816e45324520cff5816e85324520ffe1304855324520ffe1704855324520ffc5734855324520ffc5834855324520f7e5934855324520efe5a34855324520efe5a74855324520dfe4b84855324520ffd1304855324520efd5a34855324520edf5a74855324520dbf4b86055324520d7f4b96055324520efe9a05095324520ef6da05495324520ff65815495324520ef6dba5495324520efe9a05495324520ef6da55495324520ededa75495324520d7ecb95495324520afedca5495324520b7f5c12e55324520f76d522e55324520e7eda22e55324520b6fdc62e55324520f7e5216e55324520e7eda26e55324520e77da56e55324520b5fcc76e55324520c7fdba6e55324520c7fcb96e95324520a7fcc96e95324520dfe521aed5324520cfeda2aed532452097fcc9aed532452097fdc9aed53245208ffdcaaed5324520efe5a34855424520dfe5b34855424520ffa5844855424520efe5a74855424520ffa5815095424520efada75095424520dfe5816c95424520ef79a054d5424520ff652154d5424520ffa5815097424520efada45497424520ffa5215517424520efe5a34865524520dfe4b34865524520dfe4b84865524520efd5a34865524520dfe4b26065524520d7f4b96065524520efe5a34857524520fdf1706057524520efada45097524520dfadb45097524520ededa75097524520ff65815497524520dfe5216cd7524520cfeda26cd7524520dfe5216d17524520cff9a26c08524520efe5a34848524520dfe5cb4848524520dff1b04848524520dfe5b24848524520efd5a34848524520d7f5b948485245209ff5cb4848524520dfd5216cc8524520cfdda26cc8524520d7dcc96cc8524520cfddca6cc8524520cff9a06cc8524520dfe5216cc8524520cfeda26cc8524520cdfda76cc852452097fcc96cc8524520dfb5216d08524520cfbda26d08524520def5216d88524520cefda26d88524520ddf5216dc8524520cdfda26dc8524520cff5216e885245208ffdc26e88524520))) else (if i<34 then (if i<32 then 0x8161a0afc057582b6815920ac4055982a8815220a80053782978149a0a3c04f18262812f2095c04a5824e8123a08f4046b822e8113a088c043d820b8103a080003f181f480f8207a403c381d780e2206f4036581ae80d2206680313818580bda05d002d3815680a1a04fc02638124809020470022f81138087a042c020d8102807f203e801e580ee807520374019f80cb8063a02f4017180b48058202b0014f80a3804fa026c012d809280472022800f980788035a017800a1804c801e200a4004980118006a0000afecc86d52124d20afecc56e12124d20eff2884415124d20a7fcc76d59124d20a7fcc86d59124d20a7fcc76e19124d20c7fe88aed9124d20efea884415224d20efe8b84415224d20efea884c15224d20efe8984c15224d20efe8b84c15224d20ef6e885455224d20ef6cb85455224d20efe9306055224d20efe5316055224d20afeccb6055224d20afeecc6055224d20e3fd986055324d20c7fcb96055324d20ef6d815495324d20ef6e885495324d20ef6c985495324d20ef6cb85495324d20ef6d522e55324d20aefdc62e55324d20c7fcb96e55324d20cff8b94c18524d20efe9304858524d20cfedcb4858524d20efd9304c58524d20efe5214c58524d208ffccb4c58524d20a7fccb6458524d20a7fdcb6458524d20a7fecc6458524d20ef791054d8524d20ef6d2154d8524d20e77cb954d8524d20e77cc954d8524d20cfed216cd8524d20c7fd916cd8524d208ffdc16cd8524d20c7fcc96cd8524d208ffcc96cd8524d208ffdc96cd8524d208ffecc6cd8524d20cff910aed8524d20cff930aed8524d20cfed21aed8524d20c7fd91aed8524d208ffcc9aed8524d20c7fcb84c59524d20e77e885459524d20e77cb85459524d20e7f5316059524d20c7fccb6059524d20a7fccb6059524d20a7fecc6059524d20c7fe886c59524d20c7fcc86c59524d20c7fcb86c59524d20a7fcc86c59524d20e77d5160d9524d20c7fdb160d9524d20a7fdc160d9524d20c7fccb60d9524d20a7fccb60d9524d20c7fdcb60d9524d20a7fecc60d9524d20c7fd816cd9524d20c7fe886cd9524d20c7fcc86cd9524d20c7fcb86cd9524d20a7fcc86cd9524d20c7fcb86e19524d20c7fd81aed9524d20c7fd83aed9524d20c7fe88aed9524d20c7fdc8aed9524d20c7fcb8aed9524d20a7fdc8aed9524d20cff8b84419524d20cff8b84c19524d20cfecb84859524d208ffccb6059524d20c7fcb86459524d208ffcc86c59524d20a7fcc960d9524d208ffccb60d9524d20a7fcc864d9524d208ffcc86cd9524d208ffdc8aed9524d20a7fdc154d9824d20c7fd53aed9824d20a7fdc8aed9824d20a7fcc954d9824d20a7fcc86559824d20c7fc986d59824d20c7fc98aed9824d208ffdc8aed9824d20a7fdc154e9924d20c7fcb854e9924d20 else (if i<33 then 0x17318b9785c6a2e30170f8b8385be22de016e18b6f85b5a2d9016b98b5885a8a2d3416858b3e859ea2cf016758b36859aa2cd016658b2e859522c9816498b20858fa2c7816398b18858a22c4c161d8b0a8584a2c2016078b028580a2c0015fd8afd857e22bec15f38af8857a22bc015d78ae7857322b8815c18adc856c22b50159f8acb8563a2b0c157d8aba855b22ab0154f8aa3854fa2a6c152d8a928542a2a0414f98a78853a229b414d18a5b852ba294c149d8a4a852322908147b8a398517a28ac14478a1f850c22844141389ff84faa27ac13cd89df84ec2275c13a589cb84e2226e8135f89ab84cf22644131f898b84c3a26181303897d84bca25e012e7896f84b5a259c12c5895e84aa22534128589358494224781233890f8481223e011e788ef8475a238411b988d28465a231c118588bb845ba22cc114b889e844d2225811178881843ba21cc10dd8864842d2215810a3884d8420220d8106988308416220ac104d88228410a2074103788178409a203c10158806840121ff80ff387f583f8a1fb40fd187e483f021f7c0fbb87dc83eda1f5c0fa587ce83e6a1f300f9587c983e421f1c0f7f87be83dd21ee40f6f87b383d7a1eb80f5387a583d0a1e800f37879a83cb21e540f27878f83c721e280f0b878483c1a1e080ef5877983baa1dc40ecd875c83aaa1d440e93874583a0a1cf40e65872e8393a1c740e1f870b8380a1bf40deb86e88370a1b740da586d18366a1b300d8f86c3835fa1aec0d6d86b2835721aa80d3f8698834a21a340d058681833ea19f00cef86738339219c40cd986688333a198c0cbd86548328219240c7d86378319a18bc0c5586208309a183c0c0385fa82f9a17bc0bdb85e982f2a17900bbf85d582ea217400b9d85cd82e6217200b8785bf82dda16dc0b6585ae82d5216980b43859d82cca16600b27858f82c5a161c0b05858182c0215f00aef857682baa15d00ae5857182b8215bc0adb856c82b4215900ac5855e82ad215580aa3855082a7a15380a93854582a0a15000a778537829b214c80a5b852c82942149c0a45851e828d214640a2f8516828aa14500a1f850b8285214180a098500827e213e009ed84f58278a13b409d784e782732138809c184dc826da135c09a584ce826521318098384bd8259a12bc095584a682512127809338492824721228090b8481823ea11e408e9846d8231a117c08b584568229211200887843f821da10dc0865842e821521098083784118206a1024080383fd81f9a0fbc07cf83e381efa0f5407a183cc81e420f10077383af81d420e900739839881c5a0e1c06f3836c81afa0d5406958343819fa0cec066d8332819720cb4065183248191a0c7c063b8319818aa0c2c060182fc817c20bd005df82ee8176a0ba405cf82e3817120b7805b982d8816a20b40059782c7 else 0xa4aa5244291994888a3da51dc28df946b8a33a518c28bd944b8a22250f4287194348a18250b0284394178a09a500c27fd93fa89fb24fc827cf93e389efa4f6c27ad93d289e724f28278593b589d8a4ea8274b93a189cba4e4c271d938a89c024df026ef937089b4a4d8826bb935689a924d382693934589a0a4cf42671932b898f24c44260192f9897924bac25c192d9896aa4b38258d92c5895f24ad0255f92a5894f24a5c251f928b8940a49e824e592718936a49a424cf9263892fa497824b392558928a493424919241891d248d824579227890ea48642429920a8903247fc23f591f088f32477023a391c488dd246c0235791a788d1a467c233b919988cc2465c2325918888c0a45f422e5916b88b3a458022b7915488a9a453c2295914988a2a4510227f913b889ba44b42251911e888ba4434220590f58875a438421a790cf8865a431c218590be885d242d8216390ad8854a4288213b90968846242202107907f883da41e820eb90748838241bc20d5906688312416020a7904f8825a411c20859041881ea40e4206990278811a407c20359016880924038201390058800a3ff41ff18ff787f9a3fbc1fd58fe687f123f781fb38fd587e8a3f341f918fc187dea3ee41f698fb087d623e7c1f298f8d87c4a3dfc1ef58f6d87b4a3d941ec18f5c87ac23d5c1e998f4887a223ce81e6b8f318796a3ca41e3d8f178789a3c3c1e158f03877fa3bec1ded8ef2877723bb41dd18edb876ba3b4c1d9d8eca876323b081d7b8ebc875da3ae81d718eb7875b23ad41d678eb28758a3ac01d5d8ead875623aac1d538ea88753a3a981d498ea3875123a841d3f8e9e874ea3a701d358e99874c23a501d1f8e8b874523a241d0f8e868742a3a101d058e7e873ea39e41cef8e6d8734a39941cc18e5c8729239201c758e368719238b81c418e168709238381c138e088702238001bf18df486f9a37b01bd58ddd86e82373c1b9b8dc986e42371c1b858db886dba36cc1b5d8daa86d1a36701b238d8786c3235f01ae98d7086b4a35a01ac78d5c86ada35501aa58d4e86a5235181a838d40869fa34ec1a738d38869ba34d81a698d338699234c41a5f8d2e8696a34b01a558d298692a34901a458d2186902347c1a3b8d1c868c234501a1f8d0b8683a340c19fd8cfa867b233c819db8cec86742339019bf8cdb866d2336419af8cd6866923344199f8cce8666a333019958cc68662a3304197f8cbe865d232d819698caa86532329419478c9f864f23268192b8c9486482323019158c8986442321c19058c81863ea31f018ef8c768639231c418d98c6b86352319818c98c60862fa316c18b38c55862a2314018978c47861ea30e418698c308616230a018478c1f860da303817fb8bf985fc22fdc17e58bf185f522fa417c98be085ee22f3c17958bbd85d822e98)) else (if i<36 then (if i<35 then 0xd279e898f3fa79d43ccf9e5d8f29a79483c9b9e468f1e278e03c559e178f0b278483c1b9e098f02a78103bff9dfb8efd277d83be39ded8ef6277a03bc79ddf8eeda775c3ba59dd18ee6a77243b8f9dc38edfa76ec3b6d9daf8ed42769c3b399d988ec7276043af99d7b8ebba75b43ac59d5b8eaa275403a9d9d4d8ea4a75143a879d3c8e9aa74b83a599d258e8f274683a2b9d118e86a74183a039d008e7b273b039d59ce68e712737839b99cd58e672733439859cbb8e58a729c39339c8f8e42a71ec38f39c758e38a71a838bf9c558e28a713438919c3e8e1a270c0384b9c1e8e0ea706438299c108e0626ffc37f59bf68df626f9437c19bd98de926f44378d9bbf8ddaa6ec4374d9b9c8dc7a6e2037019b798dbaa6dac36c79b598dac26d50369f9b4b8da526d1836839b408d9e26ce036679b2f8d95a6c9036399b128d85a6c0435ed9ae98d6fa6b5435959ac68d6126ae0354f9aa38d4ca6a5435219a868d41269ec34ed9a6c8d35a699c34c59a618d302697c34b59a598d2c2695c34ab9a548d29a694834a19a4c8d2426910347f9a3b8d1ba68cc34639a2d8d14a689434419a1f8d0f2687434379a1a8d0ca6860342d9a128d0726828340599fe8cfd267d833e399f08cf6267ac33d399e88cf22678033b799d78ce9a673c339599c98ce2a6710338599be8cdd266a8335199a48cd026670332f99938cc62661432fb99798cb9265b832d399628caf2656832ab99518ca6a650c327799348c98264a43243991d8c8b26448321599038c7fa63e031e198e68c6fa636031a798c98c61262f8316d98b28c55a62a8314598988c4a2622830ff986f8c342618430a798468c1e260e0306198268c0fa606c302198038bfca5fe02fe797ef8bf725fa82fcb97e18beea5f642fa997ca8be325efc2f6997ad8bd325e582f1d978a8bc025dd82edd97648baea5d582e9d97478ba1a5ccc2e5d972a8b9025c702e23970d8b8325c082dfb96f98b7aa5bb82dc796df8b6da5b682dab96c58b5da5ad02d4196998b4925a382d0d967f8b3da59e82ceb96718b38259b02cd596668b31259542ca1964c8b21258f82c73962f8b15a58902c3f96188b07258042bf995f88afba57cc2be395ed8af32577c2bb595d38ae9257442b9f95ce8ae6a57302b9595c68ae1256f82b7995b88adba56cc2b6395b08ad7a56b82b5995ab8ad5256a42b4995a08ace256602b2795928ac7256282b0b95848ac0255f02af595768ab9255c42adf956b8ab3a558c2ac3955d8aaca55602aa795528aa8a55402a9d954d8aa62552c2a9395458aa0a54f42a7195348a98254bc2a5595268a92a54842a39951b8a8ba54582a2395108a862542c2a0795028a7f253e829eb94f18a78253bc29d594e68a7125378299b94c98a62a5310297f94bb8a5ba52c0295d94aa8a5325288293b94998 else 0x9829cb04e4fa723938e29c604e27a70f938429c104e05a6fe937d29bd84ddda6ea9371a9b7c4dafa6d39367a9b2c4d8da6c2935f29ae84d71a6b1935529a984d43a69d934ca9a484d1ba6899342a9a044cf9a678933a299c04cd7a6679330299704cafa6539327a992c4c8da642931f298dc4c65a62b9312298684c1fa60892ff297e84be5a5ee92f5297984bc3a5dd92eca97544ba1a5c992e2a97044b73a5b592d8a96b44b51a5a492cd296584b23a58d92c4a96144b01a57992baa95c44adfa56b92b3a958c4ac3a56092ae2956c4aada55592a8a95344a97a54792a3295084a7ba5369299294a04a47a51f928aa94444a19a508927f293f449f1a4f49278293a449c9a4dd926ca9348499ba4c69261292f84973a4b59257292a8494ba4a1925029270492fa4939247a922c490da4829240a91f448f1a4749239a91bc48dba46c92342919048bfa45b922a291404891a444921ea90e4486fa433921329070482fa4139206290204807a40291ff28fe847eba3f191f6a8fa447c9a3e091efa8f6c47ada3d291e728f284791a3c791e328f144787a3bf91dda8edc476ba3b491d9a8ec84761a3ac91d5a8e9c474ba3a491d1a8e884741a39f91cda8e504713a38891c228e0c46fda37a91bb28dd446dba36991afa8d6c46ada35591a8a8d404697a34791a1a8cfc4675a333919928cb84659a322918f28c744631a314918828c30460fa303917fa8bbc45d5a2e9917428b9045bfa2db916d28b58459da2ca9164a8b144587a2c29160a8b00457da2bd915e28aec456da2b2915728ab44557a2a79151a8a7c453ba29c914da8a684531a294914828a3c4515a286914128a0444f9a278913ba89d844e3a2709136289a044bba259912c2892c4493a2459120a88f4446ba2319118288b04455a2269111288844439a21b910ba884c4423a20d9103288144401a1fc90fda87dc43dfa1ee90f52879843c9a1e090eca876043a7a1cf90e7287284385a1c190dea86f0436fa1b390d9286b84353a1a590d0a86684331a19490c82863c4315a18690be285e042e7a16f90b5a859c42cba16190b02857042afa15690a9285384293a14590a0a84f44271a1349099a84bc4255a1269091284844233a115908a284404217a107907d283c041d1a0e4906ea837041a9a0ca9063282fc416fa0b39057a8294413ba0939046281fc40f5a0769039281c440cda05f902aa81384099a042901aa80c44059a025900f280744025a0088ffda7fdc3fe59ff18ff6a7fa43fc99fe08fefa7f6c3fad9fd28fe727f343f919fc48fe027efc3f6f9fb08fd627e883f359f998fc7a7e203efb9f738fb4a7d7c3ea99f4a8fa4a7d143e819f398f97a7c883e3b9f138f87a7c203e079eff8f7c27bc43ddf9ee88f70a7b803db19ed18f66a7b303d839eba8f5ca7abc3d499ea38f4e27a543) else (if i<37 then 0x35b01698092c0386013b0059800abff45ff1aff497f6abfb05fcfafe397efabf6c5fadafd297e72bf285f8bafc197deabef05f6fafb397d7abeac5f4dafa297cf2be685f2baf9197c6abe245f09af8097be2bde05ee7af6997b2abd845eb9af4f97a2abcec5e61af299792abc845e39af18978a2bc405e11af0497802bbf05de9aef097762bba05dc1aedc976aabb385d93aec2975f2baf45d71aeb497582bab05d4faea3974caba545d21ae899742aba045cf9ae759738ab9b45cd1ae649731ab97c5cb5ae5697292b9385c93ae459720ab8f45c6bae2e97152b8985c43ae1d970b2b8485c1bae099702ab7f85bf3adf296f72b7a85bd1ade496f02b7705bafadd396e7ab72c5b8dadc296df2b6e85b6badb196d6ab6a45b49ad9a96c9ab6245b03ad7d96bcab5c85adbad6996b12b5785aadad5296a42b5045a79ad3b969bab4cc5a5dad279691ab47c5a35ad1696892b4385a13ad0596822b40059f7acfa967b2b3c859dbace99672ab39059c5acde966d2b35859a3accd9664ab314597bacb996592b2b85953aca59650ab274592bac919646ab2245903ac7d963cab1d458dbac699632ab18458b9ac58962a2b1345891ac44961eab0e45863ac2d9614ab0945841ac1996092b0385813ac0595ff2afdc57e5abee95f52af9857c3abdd95ecaaf5457a1abcc95e42af10577fabbb95dbaaecc5757aba795d1aae705729ab8d95c32adfc56efab7395b7aada056c7ab5f95adaad6856abab5195a6aad245689ab40959e2ace05667ab2c9592aac6c5627ab0f9585aac1c55ffaafb957d2abe455e9aaf095762abac55c7aadf956daab5c55a5aace95652ab18557daab79556aaaa45549aaa0954e2aa605521aa899542aaa0454f3aa789538aa9a854cbaa61952eaa96454a9aa5095262a9205487aa3f951aaa8c45453aa22950daa85c5425aa0e95052a8245409a9fa94fb2a7c853dba9e994f2aa78453b9a9d894ea2a7345391a9c494e02a6f05369a9b094d62a6ac5347a99c94cc2a650531fa98b94c0aa5f452f1a97494b82a5a452c9a95d94acaa55452a1a94c94a42a5105279a938949a2a4c05257a9279491aa470522fa9139487aa42c520da902947f2a3e851eba8f19476aa3a451c9a8e394712a37851b3a8d5946a2a3405197a8ca94632a308517ba8b9945aaa2c4515fa8ab94552a2985143a89d944caa2545121a88c94442a21c510ba881943d2a1c050dda86494302a17050afa84d9424aa1145081a83694192a0c45059a82894122a0805037a817940b2a048501ba8099402aa0044ff9a7f893fa29fc04fd7a7e793f1a9f884fbba7d993eaa9f444f99a7c593df29ed04f5fa7ab93d3a9e8c4f37a79793c9a9e3c4f1ba78993c2a9e104effa77b93bba9dcc4edda76a93b329d7c4eb5a75693a929d384e93a74593a0a9ce84e6ba73193 else 0x42e290713fb8989c472e21c710bb8819c3eae1f070efb8739c362e1ac70cdb8629c2f2e16870abb8519c26ae1247089b8439c1fae0ec706db8329c15ae09c7045b81e9c0d2e04c7017b8079c01ae0086ffbb7f99bfaadfc46fd9b7e89bf22df8c6fc3b7dd9becadf606fadb7d29be72df286f8bb7c19be02def06f6fb7b69bd92deb86f53b7a89bd3ade986f43b79d9bccade546f21b7899bc2ade046ef9b7789bba2ddc06ed7b7679bb1add7c6eb5b7569ba7add206e87b73f9b9dadcdc6e65b72e9b952dc986e49b71d9b8cadc546e21b70c9b842dc106df3b6f59b78adbb46dd1b6e49b71adb7c6db5b6d69b692db386d93b6c59b622db006d77b6ba9b59adabc6d4fb6a39b4fada6c6d2db6929b472da286d0bb6819b3bad9cc6cddb66a9b34ad9946cc1b65c9b2c2d95c6cabb6519b26ad9246c8fb6469b212d8f86c79b6329b172d8a86c4bb6219b0d2d8586c23b60d9b04ad8146c01b5f99afaad7c46bd9b5e89af22d7746bb1b5d49ae9ad73c6b8fb5c69ae12d6f86b73b5b59ad8ad6b46b51b5a19acead6586b23b5909ac62d6206b0db5829abdad5dc6ae5b56e9ab52d5986ac3b55d9aab2d5486a9bb5499aa2ad5046a79b5389a9a2d4c06a51b5219a8ead4586a1db50a9a81ad3fc69efb4f09a762d3a069c1b4dc9a6c2d350699fb4cb9a63ad30c697db4ba9a5b2d2c8695bb4a99a52ad2846939b4989a4a2d2406911b4849a3ead1e468e9b4739a362d1a068c7b45f9a2dad15c68abb4519a26ad1246889b4409a1e2d0e06867b42f9a142d0786833b4159a08ad0346811b4049a002cff067e9b3f099f4acf8867bbb3d999eaacf446799b3c899e22cf006777b3b799d9acebc6755b3a699d12ce786733b39599c8ace346711b38499c02cdf066efb37099b62cda066c7b35f99adacd5c66a5b34e99a52cd186683b33d999caccd46655b32699912cc78662db31299872cc1c65ffb2fb997bacba865c5b2de996d2cb5865a3b2ca9964acb206587b2bf995dacadc655fb2a899522ca68652bb29199452ca1864f7b2779939ac9b064cfb25d992cac954649bb249991fac8e06467b22f9915ac89c6445b21e990d2c8586423b20d99032c80863fbb1f998faac7c463dfb1ee98f52c79863bdb1da98eb2c748639bb1c998e2ac7046379b1b898da2c6c06357b1a798d1ac67c632fb19098c62c6206307b17f98bdac5dc62e5b16e98b52c59862c3b15d98acac55462a1b14c98a42c510627fb13b989a2c4c06257b1279891ac47c6229b11098862c4206207b0ff987dac3dc61e5b0f19876ac3a461c9b0e0986e2c36061a7b0cf98642c310617fb0bb985bac2cc615db0aa9854ac2946141b09c984c2c250611fb08b9843ac20c60f7b0749836ac1a460c9b05d982b2c14860a1b04c98242c11c6085b03b981bac0cc605db02a98132c08860)))) else (if i<44 then (if i<41 then (if i<39 then 0x9c260a12cb09488495c243a11fb08d4845bc226a10fb0860841bc209a101307f883edc1efa0f5b079083b9c1d8a0e8b07288385c1bba0da306c08351c1a1a0cd3064c831dc18aa0c1b05f082efc173a0b6305a082c7c15fa0adb055c829fc14ba0a2305008277c131a0953048c8231c111a086b04248203c0fda07cb03d481e1c0eca072b037881a7c0cca062b03048167c0a9a051302788133c08ca042b01f880edc072a037301a880cbc061a02bb01348091c044a021b01088081c039a01ab00c48053c025a010b00748037c01aa00cb00608021c006a0012fff87ff3bff59ff8affb47fcbbfdb9febaff407f97bfc79fdeafed87f5dbfaa9fceafe587f23bf8d9fc4afe147f01bf7c9fbc2fddc7ee5bf6e9fb6afd987ebdbf5d9fae2fd6c7eadbf4f9fa5afd1c7e7fbf389f9a2fcb47e51bf279f91afc887e35bf169f892fc2c7e0dbf029f7f2fbe87debbef19f76afbb07dcfbee39f6fafb6c7dadbed29f672fb1c7d85beb89f5a2fac07d57bea79f51afa7c7d2fbe939f47afa147cf5be709f362f9ac7cc7be5f9f2daf95c7ca5be4b9f23af9007c77be379f19af8bc7c55be269f0faf86c7c27be129f072f8287c0bbe049f002f7f07befbdf09ef4af7947bc1bdd99ee92f7387b8dbdc29edf2f6dc7b5fbdab9ed3af68c7b3dbd9a9ecb2f6487b1bbd869ec12f5f87af3bd759eb8af5b47ad1bd649eb02f5707aa9bd509ea62f5147a75bd339e97af4ac7a53bd259e922f4747a2bbd0e9e852f4187a03bcfa9e782f39879bdbcda9e682f330798fbcc39e5faf2ec7973bcb59e58af2b47951bca79e51af27c793bbc969e4aaf244791fbc829e3daf1d078d9bc689e322f17478abbc4e9e23af1007877bc349e182f0a47849bc209e0faf06c782dbc0f9e072f028780bbc049e002eff077efbbf09df4aef9477bbbbd99deaaef387793bbc59de0aeee87765bbab9dd22ee807737bb979dc9aee3c7715bb869dc12ee0476f9bb789dba2edc076d7bb679db1aed8876bbbb599daaaed447699bb489da22ed007677bb3a9d9b2ecc8765bbb299d92aec90763fbb1b9d8baec4c761dbb0a9d832ec0875f5baf69d792ebac75cdbae59d6f2eb6875abbad19d66aeb30758fbac39d5faeaf87573bab59d58aeab47551baa79d51aea7c7535ba969d47aea2c7507ba7c9d3aae9b874cdba629d2dae95c749fba4b9d23ae9007471ba319d152e88c743dba179d09ae83c740fba009cfe2e7e073e7b9ef9cf72e7a873cbb9de9ced2e74c739db9ca9ce32e7087381b9bc9cdc2e6d07359b9a89cd22e6807337b9979cc82e6247303b97a9cb9ae5b072c9b95d9cab2e53c728fb9409c9e2e4e07267b92f9c95ae4907239b9189c88ae434720bb9019c7eae3e471e3b8ea9c732e39471c1b8dc9c6c2e350719fb8cb9c652e3187183b8c09c5e2e2d47161b8ac9c5 else (if i<40 then 0xb2f9c97c5cbdba5ebb2f409791cbc4a5deb2ed89763cbaaa5d332e889735cb99a5cab2e449719cb82a5c0b2ddc96dfcb6ea5b532d9896c3cb5da5acb2d48969bcb49a5a2b2d049679cb38a59a32cc09657cb27a591b2c7c963bcb1ca58c32c509625cb0ea58532c189603cafaa57832bbc95d5cae6a57132b7895adcacfa56432b10957fcabba55bb2acc955dcaa7a551b2a70952fca93a547b2a209507ca7fa53db29dc94e5ca6ea5353298c94b7ca57a52832930948fca43a51fb28ec946dca32a517328a89451ca1ea50d328589423ca0da504b28149401c9ffa4fdb27e893ebc9f4a4f8327b093cfc9e3a4efb277893adc9d5a4ea327409397c9c7a4e1b26fc9375c9b6a4d9326b89353c9a5a4d0b26749331c994a4c9b263c931bc989a4c2b261092ffc97ba4bbb25d892e9c973a4b7b25ac92cdc962a4af3257492b1c954a4a9b253c9295c946a4a1324f89273c938a49a324c09257c927a491b247c9235c916a489324389213c902a47f323e891ebc8f1a476b23a491cfc8e3a46fb236c91adc8d2a46732328918bc8c1a45eb22e49169c8b0a456322a09147c89fa44db225c9125c88ea445322189103c87aa439b21a490c3c85da42b32148909bc849a41fb20ec9067c82fa415b20909039c815a40732028900bc801a40031ff08fefc7f6a3fab1fc48fdfc7eba3f0b1f748fabc7cea3e3b1ef48f65c7aea3d231e748f31c78ea3c531e188f03c77da3bb31dc88ecfc760a3ab31d308e83c73aa39831ca48e3dc717a386b1c0c8dfdc6faa37cb1bd48de1c6eca37431b908dc5c6dea36d31b648da9c6d0a36331b088d7bc6b9a35ab1aac8d4dc6a2a34f31a688d2bc691a346b1a248d03c67da33cb19d48ce1c66ca331319788cadc652a327319288c8bc641a31eb18e48c69c630a316318a08c47c61fa30c318448c13c5ffa2f9317b88bc7c5dfa2edb175c8b9fc5cba2e3b17008b77c5b4a2d6b16988b3dc597a2c8316308b09c580a2bcb15d48ae1c56ca2b4315908abfc55ea2aa315408a97c544a29eb14e48a69c530a294b14948a41c516a287b141489f5c4f3a277b13a089c7c4d9a26ab13448999c4c2a25db12c4894dc4a2a24f31268892bc491a246b12248909c480a23e311d488e1c46ca2343119088bfc458a22a311348891c444a220310f0886fc430a21631094883bc419a20931038880dc3ffa1fdb0fc487d3c3e5a1f0b0f8087bdc3dda1e9b0f308789c3bda1db30ebc8755c3a6a1d130e608721c386a1be30de086e7c372a1b730da886cbc361a1aeb0d7086afc356a1aab0d5086a5c34ba1a3b0d0c8671c334a196b0ca48643c31da18cb0c548621c30fa185b0c1c85f9c2f8a17a30bc085d7c2e7a171b0b7c85afc2d0a16630b148581c2b9a15930aac854dc29fa14db0a508519c288a14230a0084f7c274a138309b084c else 0x7a05028490801282818106470457b16414860249080002060b0304c1826001382091084e0820ee138209c1041882c0c1010484830270413820941040020609800400000000000c0c13c5082a3820dc106e09548400030304e0820ea1007b85f14200f7090604151c1003706a3824101000000347049242020c0808302f04120c08004b21348082a3820a8e081818201f40cef84820201010080b0305818201a0180de360608db04818235211a90b03041b4148435211a90b03047142c0c17000806043dc1bc40de07a0a83706082906a382b52105203f02818db06a382c0c1182081b85a382e00100c08068060378c1bc0f41506e0c1407092c8290aa3820a407e0503a8e08290398aa382352195903f0281b0305a382d1c1606081f83e0140c0fc1f00a060c605023060e4701e88c00209403c07c018402108251dc65000610128ee32800308094771940018407d00c073183e8060398cee00f4416c14df0a6f84c0021be102310537c203c50801882010104603b0281e5000601f0d37c209210080804040020608181820008081818201018080ad4841883010104a0c040602020c41030305020281018080814860203010105f080674c016f5b62401400f9fadba6005108c1129200a0e09214b800c1011857142018082201e05e00c182080f092e003048089702398098004c8c12b2e00b4078030c07214044b8125c00608f14278a104a05e115c02508128104030606804f17001808844c600c05e1224a25a5c0ce60289297003c34094b80591806002a5c11302c9471420b20940bc32042b8112492595c0c0a3f140d0ae00fc07cc051f8a06857007e03e63c5082515c00f00610ae007803012889e81606081c85818207216060b03040e42c0c10390a5000608c002042104a1b8ca000c20250dc65000610018294014220084a01980040842c0c1037098304c0026001021081b84f14260c1300082500f01f006100842094771940018404a3b801e01520251dc00f00a90124209a07e05f9400945065fb600c059ca004a301184197ed8030167280128c38a1ca000cbb601524dfca6fc337d09bdfcdeba6f3b378c9bbdcddaa6eb337489b9bcdc9a6e2b37049b73cdb5a6d8b36b49b51cda1a6ceb36649b29cd93a6c7b36209b07cd82a6bf335f49af7cd77a6bb335c89ad5cd63a6ae335609aa7cd4fa6a7335289a91cd47a6a1b34f09a6fcd33a697b34ac9a4dcd22a68f334689a25cd0ea6853340c99fdccfaa67b333c899dbcce6a66fb337899b3ccd5a667332f89973ccb5a658b32b49951cca4a65033270992fcc93a647b322c990dcc82a63f331e898ebcc71a636b31a498c9cc60a62b33148989bcc49a62433110987fcc3ba61bb30cc985dcc2da616330ac984dcc22a610b30809837cc17a609b303c9815cc06a60132fec97edcbefa5f5)) else (if i<42 then 0x81242003c0341001286e328003080943700180e64000564200203041340a00f4604060a0304418203c0a4201e052100f0ac8290c1bc07814860a8e04b034180b0268814820100a420203040301484004a05210101820b21059082c84003b60800000000000000000940100000000040c1606098304c002704122109c104564270411a90b03040412120c09c104a082000000b210000000181820059080040c1059083a805241486092100016420606082c84040c10590800003030400b2103030400b210303040060608016420058080124206060ae285818202c01809a35c50b030471420b210590b03041642c0c103fea0149030220402901f800814152a420025484003e07a2005484c182600104a01e03e00c201084128ee00541c88094771940018401e3b815918251dc00603990008c07604c3025485c0039400a4270008ac829080018100d05210060290812420940a42031081f8250290f238200000202000323820621008080924200008182c0c1001e046e0200103040000000000060012590b0304f1420a8e0836d8255210390b03040e4201a1206081c8581820781a8e00c03d181b85818206e1606081b848183b6dd400180a441a90b03056082c0c1ea040c1004040336daa800548352103708d4840dc2c0c118208e285818209bb6c03e3037080981e8803039400a4201f03d102900f8814803007c607a0180a430e004d03f1b800728014846b20a4200060403414840180a4204a03005218251ac0290f238369007ee340a4406fb4803f0282010302f8a10206050e428181038305188281013a909830402020959406b2304a052107b9ea8740c0f4388f5407c807e7521d00a440f73d50e81811843dcf543a0607e7521d00a443d50b90e81804040dc20941052359450180604058030134607a0a8274809ea840c014840c411b60c0402901f81410f540fc436c100809ef81e81f8c7d01340fc67be07a0a431b60811847d00f40fc669207a07e31b6080406020209536d940018404a0f70731802e42f8a1005c8503020c8e081020391c103e0a1b850dc286e1008098004084206e1037081b84f14201010000004b082504a08200000000182a408009410035203a90100250483020941054704046e100112420049082484000025029080892100c0d470062ac8d5640f409860940a42a8e081f8140aa38230410370c2c80f81e8ced8207c07a201e03e45918251dc0060399012839410b20a4300c080682908129ee216414880180a42008081fc2c8140c10b21020606164281814620804040202094100c080b0060268c0f415040c41030028101fc2c8140c0770101dc0503020022c8552020c8e0806040300580f4601813b8052100b1dc01e8c0f414840a8100c080606ed9164148776d91c8b20184c8e0c0664701ea2c901480a04 else (if i<43 then 0x20c8208320830b20a82449dc511cc051240784000000000818244614df080818204df0800000000030305a082c0013c50a6f840e001a820be2840f301a82082a0835041002a0824641a82081e603504105410400000000018002d0416820b410492429be1054105c1820798092c8415041054104150410124de2880c0010f708fa043dc2002ef8402023e810080fcc12c92590607b1402035041034105ae0240c105703f1006a42c0c16820b5c05800255217000a00840d03f3001600a1ec4a8208368290aa082b1c102d0d410403402c15c0d0a08110c0da0a4223205210d4846a42c0c1600082935c0140c1481e80a0638a1f9800b0052b80f62d4104148350415a9082955c0140da082d7016000b4105a082d041700080b01a08964ae00781489504125905215410563820a40880503a820d410416420a55700503a820b00041100a04088050204402810d4841100a04d7016000b4105a082d0416820b00050201480fc0d088100a40880504408052044028220402934102201414021004401a068200d034102200f0290c0d01484e001057028101a0290800940a4204a3580521e4106d21104148671c0a42027034101702908020263406804a3b1a052102901288190417c5081e6039041023b0720827521306080404d240d040940a4204a08293e281a0dd202068f300a43c8209c70414b2e00d067aa1030028103b041481100a067aa1ec06830340f605219ea87b01a0cc8cf543d80d087aa1ec06833d50f6034180406d202f30104a08320820064106d200580d060940a42c8209ac8250290f2e00d05904102e03f1641072e00a0407980e4104190410641043dc20101b480440281a3b04f547d00d0601a06820341f405219ea8fa01a0cc8cf547d00d087aa3e806833d51f403418ef82901f81a10020278a1076083b0402020101c820829072082752107d0281641041100a0400a0fa0503c820804041d820ec10103040c0c1030004aa43504184a81e03d1d4106a082b1c10760d410415041a8208d486128ae20780f495041a820ad4841d435041a820d410563835041059083b040c0016820b4105a0825be1a820d41056a435041076082f84ae00f4550410290d410417c2092104d03d12301f201e8390268eb7c1344c00107b07a069180407bd048c564078860c13060980049d824ec1077a0a40390c1242b8a103d00c04d1ae2847142b8a11c50f7a0390180c1b01c8460c130609800407c0f448d414a90834840202730100350737c1180ec0a0801013980947040c02092119809cc0400000000000000000000000000000000000000080d7a040a42000000000924200490800f456407c609215b60b03041dc309503c07a384a81e03d18254dc00a839126082c0c10390c250dc40f01e901f40301cc73041606083b84009210490e50029 else 0xc820a3b072082002d09830402020641023080604005a1b0608008c204617000b800415c0a042b20a420005c0403d0c12420da0940a4306d04a15805226410416901b48441052181902b8140c0c814850640a42c8208019041432080e380d0471c0a420270341000580d040da0a4200809cc046a42352106d052100404006803c04a306db1a0521800c8260c1008080d240d040da0a4200ea9fa01a0c0340d040687e80a431d53f403419918ea9fa01a10754fd00d063aa7e806830523f40341800202094104a20110293e281a0c02c1c81e86e901c8209c7041481e80d060d60600503076082901f8390c8041284002d0803072082010104d01f8b803d2441052e027a60680a4381e04113800415c0a040680a42040401725c0c12814840946b00a43c820da42208290ec1803414867bf690088050438e052101381a080b81484010103401e0251d8d0290814812809460c820be2852e0207980e410408ea1c8209d484c1820101349034102502908f547d00d0601a06820341f405219ea8fa01a0cc8cf547d00d087aa3e806830521f403419ea8fa01a0c020209410527c50341fe280580280fa5c15d202068f300a43c8209c70414b2e00d067aa1030028103a841481100a0602000d4104000111840000000001a082c0013980ea404a082f30104a08352020a012820d41040000000001a082c00168208182a40b5202504179808250415041000009412320d41075202570179808250415041002a0820921dd5052f9804a05e2808002c001449094705800257009a204a05210252ac8aa082094ab220490b00041101a4433016820a24858002d041d48016034195c026881281485504104a052155c01a0aa08208804a2a820825029088c81484c0016b8028103d0140b5200580d0657009a204a05215410556412814875700682a82081701f8aa0835700502000f01a0807809c0d07904171a027034182c81681a0c09c12a2e00300d0a02a0a42041052110e82f006029108740300f014890b20a403c3b06080a82909c6809c0a0664606827000c2c82901a0c1652e007814892900880503038005c18207980a2c851d83904138e0980052e009c14860101034028125c00f1130cc8c14850b2068221340c0344b8059281702908020271c04e06834b8027052180682908e3809c148604e0a4202705210138290809c1484092144b44922640c4b8280405c68203c04e0a4301e0991bcc0290ce80200a02e2059083b0412c20921005027100f0138290c078363410641048752e01640780d0a06803c04a3b1a052101a225a2491300f020980780d048b20a42c82081381f89164c8c40921042c85e6020c8208320828ec140c0344b80592004041282068f300a43c8209c70414b2e00a07904105203f103b040c00a059710b2050304a4b801e052242485e6))) else (if i<47 then (if i<45 then 0x81fc04098182810140808098602020dc12a90c04040fe020501018080c040218818c3010107908318680021c1d8a03e32c5082f84160340010580b0006bd01344c00160008380020101e000801c0c103000404be1e000838002000c083507b141a448be1ec528203d183b0417c395207e03e3ec508310417c3d8a0860503022c078003c00100503d17000404c1a45c001030028102f841ac1cc40b0103208040416420180682058081904124206000f00058002c001e000f000780020e000b410781820e000801d8a16820f6287b143d8bd302e000d6a81f8b80020da0a42682083b143d6dd31d8a0504ec50430281f000780020560e42e0008040400ce14df082f8517c2c0010760b000580020e000f00078003c0010080800000117c20d410080800000012420159080000000c00104a05210ac8250290c080c1002c8416020b21000382508164205cd0407e36b8082c84040c100118416420a41600082c84a08148400220801481100a0640c100118448c240c1123090304124203c1eb811a01e159025282484002000a548480020a8208acbe28816420059080000000001030488c29521001a0820b21032080000018182d0410300041642a0c1002c840202001030400b2120008258a481a0c12420eb8034149052200124240010590d4102b881642060608180020b2101030400a410590818182d040ae2030004164206060b4102b880c0010590818182d040ae2030004164206060b4102b880c00103030414820600082c84a0820b012820571000c8209210100041282f8a2b20ae30590ae28492c20b215c5080164202060ae2840c0c16820b0005714251c10520b0004714206060cea8580020b21001802909800206060b41058003d702920500604052044028180e0060803020180742000f01a08078c880d07904120101e1100804080b42e0014080168b8182f02689c000340d06402e00204d8b801f03d244106c1829041038d01381a0cc8c0d057300680a4381e041102c1803414867bf69008805047000b800415c0a040680a420005c0403d0c1b412814860959700e40a44c820da4040e0017c50b8005208207980e41051d83904101c704c0020101000f01a081480945690104a3490521da401a0807be04e068300d05211ef8138290cf7c09c14867be04e0a433df02705219ef81381a0cf7c09c148600080b8d05c6880440a4f8a068300b00501f4b8200f04c8de6014867401017034103b040b4200a04e201e201100e380d0471c0a42000b01a081b41484010101a480f01a0c1280944003401e0251836d8d0290c0692068206d05210015cfd00d060687e80a430573f4034199182b9fa01a1015cfd00d060ae7e806830004041280d0509503c07a3c820e5c0250168139009f2e00b4078128030c07000e4105f142904103cc0720820 else (if i<46 then 0x4135030416e13a90803dc2f8a17000a04043dc2818100d09d48404c20c810640809840f421dc10300825041280f52dc6060018203f4f704d18771ea880c027be103f03d13e284ea427ab16e204a0de2c5b880f423e807a07e303d34913e28400dc18b709d485ea60205010103d0a1b842dc207e14df081e85c002002c082c84086e1008081e85140275210010dc216e103f082484020207e103d08252db09f1427aab6c202a082c841d42f8a104a0c5bcee89140391c106e0cfa01f880f42892104909060a4891242096104a082484a082292103015910ac8771420602b220f50ea411f09124207a1d48082505524830409a41825590aea8771420a5b8a284a549107a8419020ea103d085b840fc207a10b70ca48404c22921062082684134309412df0ceac25081882892155984a142515b8a128adc456f094284a2b7142501f8818827be1808332122c84fd020b2104040416420b213df08320516428b214590a2c85ed812840950b2200c03f04d181e9dc0a16430b213b8081ea060a16420042c85c0030b2103c142c89030201a17b6083204190202610ee08253db0812a164407e01809a303009ef84ee027e813b8081ea06091640fc4a9014590dfa01f8800188b2200c3f415db0603020a41062087b84924240c10f70b0304c0023ee0cc418322108fb906087d483044103ee20640b03043dc241210106047dc830198650412060836840202c0c13c50832046a42010106d0b113e2843b83bbe15a90eef9250892430ca10432bc10b77c83044b21ddf08d4843d4205c02c01a30160832056a421ea106f04310378405803441ea10f509248492420de10f5080b006881f021ea10f50ad4849642f6c101600d103784194235215a9082c852a42172144908008400420641001080084004a9085c841242002e0816840018100c082484190277014a9080190204a9085c85124215213b809db0419020c810000ac202c01a201600d00c1800fc0340306018102c082c841280c004c60d8106e082c06196d2004c660c100158402021c410b708040430820052082484158281814500815850302810140c080684ea420261002c8419020c817c5080084030034409a018203f00c04d180684f54205410590818009880c0202611df081f142002103c105030201a1007085b84124200210ee02c1032041902092104909dc040042770100d3b814fa067d0201f40e47052a420f576c206e0cfa05124202607a27c50801b033e810a9080b0060803420940262c8e09acc250804c2be815f408320419030ca17c5082195e0851c481820ee0c71042a431c418e244a112c8404c2002100d0809840ac2446102b092c840ac2810056260608370602020c412df0c0405818301017a98081404040fe020407f010203f3b6808181fddb4040c0fe020407ef6d01038080 else 0x403e100d0bcc0401c2046102b0171224845642002a08158138808ec140c080685e60200e10490800843b80504634115901e10310401dc17c50811d831d481827980c750423820c4104d08268488c22b2894240c091184030201a104a0c2504e38224612230c25013880150304446100540c10acc2508a3820a309422230ceac2508015030402610620826c248813420f6107b0bcc0407820f6106f0837041b020d61808083106020301011a9087a8404c20c4106708fb8170a020301005c2808083104101005c206f083204190205810590801b4235210130815840b020b2140609dc041bc205c018201600d00c18160456420da1158083105164260c1300081710408884241005c202e20810ac841bc24181208085c842e4217211b8081604164201010590b00042dc216e10b708dc04f14216e1008080985124229210490a24841495244094100d080b0408c21ee1459080b0403420b2100508068508c2026100d08fba328028c034202c130008fb8170908c244211f702e10fa8170856420de11f702e46520821060008803420261423080684830014400006840582046101608fb8170a1940ac405c11f786502e1815840b830ca056202e0c328dc8170c0ac205c186502b1017047de1940b86056102e0c32815880b823ef0ca05c302b9a91006848182c0c130609800482024421208083b8482024102b22064083205818201a1209080001a101609041c108a08240c102c082c8581821ea16060804043a820b210620815041642c0c11f7081800608134030405410620831041642c0c102a082c8404c2c0c11580815041902172144908ac8537c216e14df08338437c209a2b2202c085c8412429be102c08ac8068250ced820de14a9087b04ee020541076083784017214c50a248456429be106f08150437c201a07e202c085b841bc21be10080a06051402040c0a0405030201a1013087a841902062100808368ac080341b4402626421a90811842c41b440da2b221a9081f1420b0103c1076a5030401a1032085b8412420de10df0836858882e4289210b9085c84124217210b90a24842e4207a3702005b842e4249210b70903042e42c0c10b9081e046e0240c10180058182c0c13c5085b841b82c0c10b708040404c2f8a15f40be285f142be811a90831076d80ad030660c1259081e840f46e40ad030837205c818302e03d40c18db815a060c0acea44c00125908ac841bc27be11a90da4029089242c0c143e08faadb081d420dc1013081e80608030201a018201303d100684ea6a38551c100ac8492420c4106f087a040c437520f5b6c302a08310404c0f4416e13df085b86020cc8401010f509d4841d4200b70c04043dc27be10f70b8005c002e00100c081f80688d6004c47be140c0a06050e43752818206e083784f7c207a1052b4810250)) else (if i<49 then (if i<48 then 0xb040b80584fa605025df0817040b81b4405c02c258e081700b080b82d70102e01613e9814080b82bbe1bc50b0006f14378a1bc50924840b8058402c1798092c8577c2d7016b808320602023e8105209ac005883d82752102701613cc01a1918c0b8ea448ec106f0803d82003432310291ac88c8c0d0471c1476087b040d1e6040a5094692303432341e19ea80b0814820a4fa606833d50818043d82016102e081f142f3013a9080584005c138e080f540b840064080d640ba128058909402c284a02e10295a40812826b2105204a10295e28811e12840a483c232341e11ea8414af14578a184a047102385e60208f609d4863d912840049080b040846102c082c8412802c46b0016206c09ac03e0816023be1b48005102c04ea42152138e00b101380b0809c014404e02c20160a3b0477c201010f6098d06c6820461002a0408c260c147608ef8402021ec10029041242016102e0e410512c283813a9080584071c1c82082c8720820c810032040202f8a1798080b04e38200a142309ea817080a820b210300051018040061904207608028477c23be103e285e60200e1001704238202810230824840058106408040419020a5690241c08290250814812840a578a204784a1191a0f08f5420a578a2bc50823c250811c20c81b48005102500588128058509402c284a0161002840a2128484610050c250170a1280b8400a1064083205e60209df09d48677d12840de17d302810320419020c817980801b031ec10a90c7b225096a420ec16000b0305800202d01020168081017404080ba020402d010201680810174040805a020405d0102016808100b404080ba0204c00140c0a0605020200a101680810174040a020205d01025a908174040a02020ec1808080b404080ba0205018100368516422b210660a2c8456420223080684009a100d00c10368488c205810590806041b409c40da06004e306d013100034201a1010604034200a4182001386638201a13000806849d8201a127609410402b2106d08ac8416420cc162202308118508c2846101f20c11250918883020b2100918483020b2141e0a118508c2504100048c260c1000c0024ec12760a2485124200490a2484029211230824840004060488c2238114b08268413403040d610620911840a820b210620ae28418c244615c508a8040c0200a81820300051006844c820c6145908a48418c22b01132081020004491c10230a248456420261023083300f00b8d12422b210620a470408c201590a470508c2058104908068403020016080a84001a018202c08ac825092382846144908ac840a82018108e08038401c205604ee34301f0834845642000c0824840b02058100004c201010ea080004c140c081129f14564681814760a060403420d274020130811840b022b2105008060407c030 else 0xa2b205c406d081a3cc1918c08c20d613df0816641080b020101052159101704034058404e0da2027016101380b0809c058404e02c202e081380b081b420da864206d08d4852a42010102e081684004e74002c300f083b041b419840d2646204908318437c205802820140804040d01b60786068646203432381e181a00f1918c148564406413230341011840ba6a41b4671c106b09ef841b415e1286068094234902c84a181a191a0f0c02c205c1c820a25841b42838100b081704198271c102cc821641040b020101052080b05f4c0d040d6184a00511ef84020271c108e086f860200fc40a4135800b142501f88f7c20163e823a90dc701f8809c0584970179803432318171d4891d427be1000097006903c3034323125c40f08148d6446460682ba904411c7051d427be105784a4b8181a0250814a128d24606864683c300b0817040f8a14b80bcc04ea42016101c70400000f5405840a4101608293e981a0cf5427aa05c20300c2501d88f7c2400107b0a24840446104908290250a48d8003b8a160009cc05124204e107b0c256e289e608784ab2105204a103d8405212840f60a4205204a1024851285244c00101444a10a490f0a754229216000cea845677144c001dc508acee28980020a5b8a203015910296a40a12b7144f30106d05204a18290250814b714408f094252321e103682b8250f7143094058215908368ac881b47545b8a1052dc512250a489800289408e202c44a10296a40a1281784f3043c255908290250814b714408f094252321e12ea8771420a5b8a284a04710a48580020f608e20470823840142292185e0c2535c098003094d7026000a2485566128058709402c207b84a12acc2500b0e1280584d70107608142250888c289216b8083b05800289405c284a016101742500b0c0a2128509405c284a08ac81742500b12566128058709405c26b8083b055640ba128058909402c202884a14250170812820b213df0a2484124204e02c71c37980343231a3b04f7c2000009c058471c10050a0410989e6028b214590800001d022c8809ce80058689214490a248412828921449081a191880d0c8e07866461028b1a11d006e60204e647730332381e101a00f0a078205c64703c02c481e016122485124209414490a24861642f301001704e382002e41e1191a0f0800000b040a1e60406013df082a0290912771440ec1449dc51029040f8a100336ef896382b521ddf20c11030488c240c106d0804058002c0c10300041ac278a15df0d410492c24381ddfa8212c7063dc1b4830605a11a90804040b424381a820eefd41096a42c001ddf24a6821eef9253410f77c929a086492106ef90409e6024b21ddf0ac70777c8785bbe1249bc512d48414820ae15a90ae285ae0205c02c2600081700b08049212230b03040c001008080) else (if i<50 then 0x216df096284b7c258a16df0b6f851602dbe16df0a2c05b7c20b0103f080b006881603c00106f0806041b40fc4dbe16df0b6f841c001ec5e98100404000e10000542002a08159060aa39a08551dc00206a0837078002000d080000210ee0141341078183c0018ea08040517c2dbe16df0f62b47081d8206012f604d136f85b7c2dbe12df0b4107b1404c5d8a07e200180403c25c5d8a26dfec5e980056b82b6f85b7c2dbe12df096f840ec202616df083585b7c20d614df0a6f8537c21ec14df086f8402021c412df086f84004205c02c01a306f080404020204df0a6f84020201a145f096f8400000685a3820001504ba825be13a909ef84f7c2752140801311d485078104407e1ab80d5c061280fc42b2195800b14ac0058980022b0016284a03f12ef87521ae040ec15a90cc701f880c0010590b5c0405a638ae0607c502e1591be28ac8800261014082c8577c20261208013102c8477c281012060903040fc20581206081604164201016000800c001239081800205413c50807840b005040580295043030004020200a10b10e8d01a080d34684068a34205908208416428821606081a05ae2078484611590341017056382bbe1da920812830502020ae1ab809118448c209210526b812250a489800229243c220008170401c22b2100709040401c200e11590823dc5940b86028160608170580020b2100808ac8402b2100a48402b210070900040202400100acbe2880058e0b8d04164200e1007090404164200e140809030488c240c102c082c8580020606081800231c1030004020200a10000c0c1600081504f14205410541058182060008040401421d41052082a040baa17c50be285f1420ec125e0ac7041d820ec12410b030675404c4c00118e081504164201016060818002b8a11650b5c041d8244616060cea8580020541059083b05ae02c0c1030081805800206010300b5c07a082bbe1052082b85078014400a7be206d4080051c040058814820167be202d0836841b420db09401633df080b5c708f7c205a105201e101440f0814a128404e02c238e0be284014207980836840002d080148204e74002c30570c0f0028805ae38404e02c202701638e18293e28170c1b42068f30646305705210368409ce8005860d613df0816040b02068646281e082901a58d0cd2414840697a6646334932381e181a036c0f0c0d0c8c406864703c3323034102bc250368c0d01284693094058303432341e1805840b8207c5083685e602016102e080e3820581001606020205c05a0da338e09ef84050205c106d4080051be2841b420da13df087b041d820d610760c5c006883d8205c10720824841b420db09401633df0805c04086a4205c102d082905f142f8a17c508368437c260011a90804040b420686462016b8e101380b0809c058e3860a4f8 else 0xb7c255))))))
def oP10 : Packing:=(4071,5,7,0,0,17,0,oP10F)
def oH10F (i : Nat) : Nat:=(if i<8 then (if i<4 then (if i<2 then (if i<1 then 0xc0000050008008042003000003c002003003800000000a03a00c80080000000010006000001002000800b0040004000000003800800c0020000000002006001000824e002001001801000f00001a8000002000009c000006001000000c008000002000c00100e002c01200000a8008002016026002c00000000002d400e00100d004400800000381180100300020024002000002800400000d000001c002000000000002a002005000001400100000000040060000018004044005001c0200030000000000006000003000a033001001c0000000020000000034014000004400300000280060010078000016001001000000000000d003001e04a0000004000031000000c00c052014000c00000000680c4000000012000c00001f00000040000030000004002003009000000800e01981800020020028004000002006000001c01a000800000402b001001c00212f00580100000120000000002000000000000a0000050000006001001003800000500e80000900010008004004019000801800e00a000009000000200a8018000000008001800c007001000000000000500081760030030004194000001000000001500080000000000000024000000002800001e00700280080160040070018044000000801c000004000801c0060030000000000006000000026400300080000000010048018042010000001c00600c004000000600b000000400a0000020040000002001800402000e00000800080010030000000000002001804c0050000000012000000000000000600000040000090000004000000019800000c00200000000000060000004004000002023000e0010030018008004000002800000d000800800000000600000500060000004000072000000000a0180030030010003002001400000e0008004000001000005800a00a0028038004015000000400000200680180040000000000000014000010000600100d0070000001003805400e007005806400000000b00080000010000098000000003805c00200c001004c00400500100000000040068000000000002000000e0010000024006000000000c00a0000040018004000000000400000a0068000000034002801400600001180000000000008000006000001801c0000000010000000001000000400400200300480e600b007004402601400180100440060000078004000000000c000004000000400000000400380000010000004002001003000000000a00f000400200000080200000000000014000002005800c0580000000008010001000800800800d00400000000000000004000000001006400000000a800000200d017001c00200100200000020000030000016000000800c0280150000000006001000000000600000080480020080000024000000005800403e000 else 0x20040000000000040000801c005000004c08000f009016c0a2001018800400200a0098048014001002835000001e0038000008001000800c00e00100f803400a00200002580580000030004068000002008001600400000000d4000003000c0000060000500000029000802c00601200780000000010028038172013002000000201300580080000780060010000000014001402e007006802c00011e006800400001005b80000480020068004008140000000800602b0000000006021000000005e00a0150004000009044001800003a00100340120220098000006000004003400001f02e0018162014000800c02e12100080d400a022001000800600a0008024000000000008000000602000b4000000007800400400700080040000010018038016000016803002c00d000001004800a000008803e00500200f80080010058014048022008000000c00100002dc036000000017800200a01180040c6005000000000400000c009800000600000b0002005000800000800b00b0008034014003001800a00901f800c0040bb0008004006000000001800002d01f810800007200100180000070270064014003000000c04e004002000001600a000001c04c0000398124052005000000402e000006000813e000003800001000502480100000000218000034000001000005a000007800c00400000700000020110000044000015001801800603f007801000202505100380f8026008008401e085003000400000100e002800400b0070008002000014000429402a0060014016115001000001800003080080d406700000000020000008068006001001800000e000002800800e0000030014002000000000401c0040008000000003000000400000300680200040000000000042000000800800000000b802000e00000001c8002003004000c03c00000280000000000020010002065035001000400000b00cc10c000000013400000b03680240000000008010000010003008c00000a006808c0580120108008002000000024c00000500180000100080008000000003008000001a00000400880020010048000004000008800000200a0148004032000000000800401500580440fc005002001c000000004001000000100200000300030000000004000006000802a000002800802a001002002000a0000000010000006000004011a00e029000000000c00f809402801f0000000000000000005800005f003000000405900a800000004a005806000001900000000040000200008000000000000c000001000001000001c00100000020210008000002000000000008600b0018008034006000000000600000180a400200500000000020110000008002002001801c002001002801800600500b0014000000000007c02c006002801800000d001800) else (if i<3 then 0xb800200009200000d40041310bf01604cf237803406400b000012402200508b801c02000b000001000001b00000400000150000000000007000000043e001000906402c000007002000a00100080100140000128000000002000003c00600101880009420a000680e800401300e002800400001b801412e0080080000000000000050c06c01000180180000031800004008008001805006400300002cc21800d000006000000200000040060000000000000006002006800000324380d45e40080680000008004017004403600100004381a622700d02e004a007008019801a00c00400181c400600d00080020640148d5806c1e6030000800c00000b000000e000000016803a0000010fc004200000100fc04c000000001c01c00700000000a4011009005038e000003800412205a0000000118003000872003200002a813003a004000002000400000180000100d70020008024003000800400a000002000800020a1ec838c00001200184b80000040000000056000000003400c00018e800001a010033000c8c6000000081c022001005800000207f196000002e1c900080003f808c015025400002e009000000200000004d80120000020aac00a001001000001801f00000044260170050080000007007000023c16f000000424812d00d8108032007004004c00803b0000000050000010803400a0000f40000006030020000400205300c002800800000480001140c7000026001600d00080080060020000004072003001006802c018000005800404e007802c00600002280140100040000070006047000001400216f00401742c60020010004042061000004800000000000d40000fa0000530052000006807400000109486402d800000303d409600701d804805c000000001404e036000004c022001000000002200000f008402405b002800000e007003000000001a0b900a40d0001004800402a0000050000000013006000400a00d0018578014000000001c042001000800001a00b001005401201e00001280aa00a00181c402a013022803000e0000000000000004009800000000000000280040000048014014004000002400000f001800800001a0058000002016047800c00000a00080001a40090000000008003005000001600200000680000090010000000000003801000e01b007003402a001000003c00e019070001004a000007000c00000700e000000201900b0054010001002805c0860b600800140060000390024034001000000000800400000b0000000001004c004008005000000a0070118010004004000003c19800500b002800600004a80080000010080058044003017000000400c000000005200a000000002400c0018000004010083001400000000200000360030060094092000000003c002007000000000000 else 0x4f0406b5e9e6f60ea8c0d41a00b7a06064032001d46012eaa0d294890da12c0c1135c0e89603f9a1b8b48a87a0f2a003dca1f734194821d33804e4013f20028a00000f0324004000000003c00000089000380020084c1800001a8fe274801c000f8c006804c04e004002142c03001000380018be00301f007c00a00000580380001310dc800c000000000003400000200180003fc0010000008000007002800400e01b00e40f4002000170c27c00c00a01d00000380e000780081b003f4e9003000a005000000011e03d00242240c47c1237006c01001a1020008000018000800002e03300002cc930007000801800000103a01f813c00a00201300002c400018e41a40074fa125406600203689a0da40c30000000050012000002000029500f000c00000001107083bc005000033c0280030078000b8a00400000000c42570018e800320463638f9400000000080100100550c2004402a01900280850a628d001800000000402d113003a00300286c0000050001001801405e0d9818000000f014001001201100300040020120000004000008001800003c00000000000000000a6801401254b000014cbce0014cd0000000003000801c46600200380000060010199a5400000000200000740000080d280046c30000000000001000802c0348110258004d8e00200000601f00010ca804c00811500100080020090858000474035012824c00000700000d800000f000007000018e25c002801a030000005008a00101e800037400600d8a40000035000000c014099005005c00001112d001400c00100b8000000000000044828600000790c000220a062800c000108000002815e00402b8008004000000001404802f03a005005218e00f8018000002003001c0d200200087fc8e200a00005fc0040000029398014001000000034e026001000801e08a00000388c200000500484d2028000000001200000d002c0000603bb811c01000000380008a401030900040000031ed001c0080252810038a226d102a1c0802800000ba180018009006804000802100d001c006005000800400e000017006803800f006001800000001503a403868b00000200084c800a000000200102500c8008000011001402e05200400241f6000000800008a0000001c8004036f00280000080000e4807010201e00d80400000610178000070000000005c0902d300008ec074031004000040600500f000c036009039001802608d0038160000005062022800400e001000000000b00a800c0000000008230016000000002002e000000002c28a026306800481c0013d8801000000d0050018042004000806403c002000000808a000119800800000000c000000402600000000025660000000074028000005c04401a000000034c00100000000320030000c6c0f400500000)) else (if i<6 then (if i<5 then 0xae61aa2019c501151a1cda817d020f3620ae821acb097b660bf129b41c07018974ec1d8600b91e9ca7ae448c082541b81e06e9c0d7b40a87c0031c984bd1f5fc0f5e40dd1a0ea3e1492c0b4989fa5a186621daa4154560449a99420860e41eda40c7541f218055b007c841334c128220bbd21563a02e8419ae296f6a07f1a019141a3a20452c01fd80b7340951405c18899ce02b30017021d23817d40086ea88d00001f288e881243a875621f36a16228122d40d1f204e2a1a64089ca28e7388ae141172a1aaac00d720e698ef136169660ec280cdf21719a1c890178a20b1b010cf002414027769a17815f2e1e868898ceeb77e4f1cc196381bcd40b13600c3219ce6013ba05ca29601a1366c197aa1f26a14348076148e30c0aa26893ea09eec12f440a0129d1400cee60a6641511a8ac60976900c43813d62064b41ef1410da21a2fc8cb2cfe728050da00a1e03b5080d7804f421c81c1a03a14f32080ce1f6761f9dc11490c2008179660d03c04dda1d81e990ee8b79a1802c1f78209cba07da819f6c0edec06a268d0d804eaa01c389ca901e07c0dfb09a1368bc389b5fe0e4a8022de1f7f20be760705c01df60862a8a8fc146280651813b021e34a98400882ce024580c4969ba2e89f9e1eac4193f20e8c08d0be043bc0f9f41850e1006e0e40412a5c97e980c7948f22412fa4016520406c96d300b6980eb02090529687814bf00839e15a041e52406fd68caf21a06e0654202f6a1e7f41737e118760732c0565c1d7160ea62108aa01d520cd021117e8b0c6127e8004b20e0e60dbfa0233a0374612750ff7840145e09ac296e2c0054e0682e13fa4102580dcb8875d01323e03d2a1b98c071340ac56084701bd440faf60b7ca13bc800895058aa0ef8c1689e0bfea157b003a260288c13baa9a856029069a80e1142c9faa2079ce07d9a10e7e0676497b9008d980bdcc030840d71604cac1a12c0b10815f8e1c95a15a860837c08fe60695c0b81c0acf60223014d3e0f6768638006394169b01fc020a518068ae160c2060d215dc60a63c061ee058b8099280b076006761966c0d398045601dc50047501723e1a46c1d67c109ac0a81408a861d9800bfdc1016819f800d2fe00ac00b6a8001681871a9ce5a12ece1dce613a780b5da89ecc0503c9dd341136a88b4a8c9bc1720e19374154ea1bbb4092088e7c801b540706699ff60e16a0f74486a7a111d00336601c6e0ac36175788aaaa0dd4803daa039321fb760610c0e42a1dd9803252191420fcf414576164620c30c2e7b48048018ae4008428c56412490151440d1c61e1648e9b21490c8ea7a184e81c12605d620a6a203d92992140eb4e023f20f63e8df0c0e83802de214b801f3160c46c178f20c904003580539c003d41777e193561c024198d202b1209b0a899ee0778095a240299c else 0xc156180929a0a9fe10b4607ad2036568c59413dd41d59811cba1bf6a1f284066e801f2e031ba16d780fb7c099b810cd805f180a64c1b4860206c0b1fc0a17e1f2ba8a7100989c1be84015921c5b6806b81382e1f5860d7d086c8e89776037f28dfc60baa21278417b9c1a452130a41c4d695b9c7f4e68c69419d540237a136ca06d62162c00815e0827a1658211be018830057d4025e61ddc60522c0ee648c66c1fca8994ce159240d7501dcbe0bf7a1240c0d7f61869e1b8e49948a1d76a0965a0912280f9e9c4c6068981ea761ec5c114b005baa1cf5e1a9c809a1810e241db820fbf61524810736091de059020aa4c0da540b2da066c40cd28017f08c764062820f2440b3881c3de9ba0899a8a135fe0196a0d79014a2a1f1a61378a0579e1eb001183c0bc9401ae21c35a0ac166ef18139901685c0d6ec0a1f81038e082101c6b818c8c04d8e889160835000e2215c5c001b80a8f619fbc170ac9bbf005b50048f20b75e172868cb641dc8c00c500b0a00e3b20a0821bce8073e40bbb61e0ee98fd09890c97e721732418d641460a14cb00f4ce11f1a8605e190c81f35c12d160764403986106cc88a060f8360de6c1691a1896a16e00107921c2d20649602be818c5c1b8c21a1b60b8c49a34607ffc065be13d800343a1b060194e611684194c8155a8102f8186f00af4e9ce369b9ac0f7621bf5a13af6079a605876041601f23e1bbee032ce0979c0dc1c11a0e1f7460b1901617c0435c11bbe1597a103d20fd6808fa417e3602ad413c40037600640e88412158b414e8419a320f180108380a0c495b5e11f66004f61a3f403cb68c50619c2c1d2e40a8da11024042121315002380111040af620c7d603d0e18ef08849c147ea088a0089dc1ede41d1341d0a604ff21fbca89d7810d8c966ca853ae0abe400438141080e98a8dc4614c560b3ba1928807d5e076b61649e0352e9ae6e071f8015dc018a20d3f6079e6000d60db981ee480977a05a4a124521184a0f9060e3fc0a58c00e4a1aa480844485fe20ed000b610054400b8be184bc0b3c203afc068cc88c608df860d4620eee6055c89d212192c413016056700ca460c21e8ee9e090c40115818e660c8c81a8ca08ace807540560c0cb48049001b086074ba161b487c9607e6a0ff8289b440889218532019480de44134c01a93800c1405dea166e29b3900f7a804c5c05a120b5ac11308019de1f5e015eba8e6680861407b961ea4297b001582a119d61cad41340e0a7461e5429741c024ae0b178898461207418fa61da9814ec84ef04181c0039cc16bbe15b401d50a86fca034d01343417ff013bf08da3c1161c0a3c80485412f2e8de3019a0e1806c17dee1ccac0666a1042c1672a0c9dc82118080561abf401ca2966ea1c8c41b0ba9b3481c5e6141260efc2035f2117c4135c80096a12) else (if i<7 then 0xd8b8040ca11bd21bed610f5a8cb9a1370e1dd481c7c6188d016d00054d09a364172d097bac06f62143aa1547c01bde1204898bcc1c32a1053c0d0880969e13e802e8d018b0c092b0168f08968e896581df2417ac21a10e1d65209f1a9a2b80e7048ea82051621277c0552e0d67e879f804c3c08d6019952142fe0a91c895228da62879cc011e00b1dc9a66215d101dcda109ce178020d0be06df215d7e08714097481585c177b211dcc012781a7f2143e21c71a002601de661a61201f4008eca0d68612d9a891341a7960c5c416a500a23687dd81e22407c4e0a27a1ae0a0dad81ab2e06a789b13e1baee9e5480100600a560038c0a1ae1e575508820d2aa0f2e8027b413290088520ba9e1b704129d61b38a0e5c49a3800bb3c1b4280a0bc00c8a0f6162e7721831c1ddaa17eba12e4e016e0960a609eb889798107b41e0380c3980521608c261add616c6e0e26c085f60ea14990b216b2416cf20f1bc87994021a4047241041214ea8080f80773a022a81c82c0923c10a068a4461b84889b92175581b31c00bac960da1264c16f9c0625a95b621a278134f61d06602ff008ba015c281e1581b1d60c6781a660105b4086661bef60f110047c0121a20f6c419bb4198ee02f300bcc4087e4033529b81e1001c1e24e0e79a88bf409d4606b301c7f20429e04d30124c80581c0550a97c54184141d25c181fa0594613a008dd1a892ba0a148153001b56c142808c6b498e2a1a74e1f50a1e9340678e8987610944109640d1860323c0cad48c30a9b6d80c8041a72604b620117496c6288d34156d08c434093580ccb815df01e1e20db5a1db0005ec40b29e8b8da8a5881c05008da80d5ae0400c0c3a00ffee17a168881a08966037200e5ee1a48a8a2849aa720b42e1e4e89aae40184c0842e0990601c0c06a881576819f02869149e8581fac40dbd2148fe08f4a0ba78055900e7e0146961027e1494617a7a11d0a0c50a001da1926c1d72407c72169840cc681d3b4106389c28c1ebae17680182e20813e022e412a7c98bfa00f161e496025bc0d5341ef708c53e0183a144b602e5a9ed648cbf60ff4888b2e127cc17f1007dcc171b601f661dc06195d4061a61bcba03ef217822141de105841f57804fa80dd8e132b88a2348a38214a6808ce60488a0d35a12be40a79807a7c10c661aa00052b488b6016dd696796080621b3d8111ec8ef581fc8c1dfec0d2521d5669c63a1e628ee922028781e7928051e094421eeac02fa889a0009abc017248a4d60740c130481bc8e0630c9646c051f009d280c2201a3181c778044001b6f2806180ddd00095e14e7c0570e0afb0104c6858b60e6148f00c1e83c183e00d4e48a94a1790c1e2be185d0071986e9860383818db010c001c2e81e94019bfe075ae985da1a0f09f9461ca4219b048a8020ddb61a05a05fb else 0x6c034741fa9c4eb900065a1c0fe1726280ef2df8d80c57c88700056a4196469a3240cce6002bc00eb806d46036b21e0ac11916020ae019a805d2e06dda084920e0a00dafe179b612eea029e40b04499ade082aa9a4f6039148ab2e05fe0005961a2d01e7041884c1232e1ecca0bc3e14fba11d9c1f3e016b0e8ce7a9818e1612e1c4841b24a163a8194160c8f20dfcc18bbe8c9de998308cbc49a0ea98042106460e6fc18bea0b76209e6401aba11fda1f1d889d48009a60166c0518a0a4841837c1bfa21104402312880b0978221b2280d43816a9c1eb3015fcc1674e14e181b5481b6301cd400a374043d40d9c20122a123c48e96c0d0ce8a69c0ad3c16cb00d0120b0fe06c2a1b79c1798a051240eb7a17d841ea2e9e79a9b79e10ca49d18a148180b40a10ae60f9940257288678112b2169f01ceca094320fd3897cdc1c5180803e0b0da0745c0784a105fa048dc1048c01e401aeee05f6a1d4429f4ee02102118d41192e0c9260ebda1847c1c8bc13964049d00235611f2e053da1e98a88a520c41e03c5a159100c60a0bb829f9d8116b4054aa8b200016aa1e68417bea07576192a41448e0a9561505e0138c1a3c61d7d40e9101621a1bf9a198341ce4e992e013e2a0b6de1a144862069d2e811b9a010c20d3b80850e1772006aea060e29a94c09e1c00b221b86a0fbda87098034be093ce172440bb141ba2006e6e1f60c0600e060948b94c1e41e13202152920800c07254194361d0d41516e01bf418588176f412b9c1cb288cbaa0debc08e9a1857c0317a00f6a1b6aa136aa982801f48a107ea08aaa0a99814dc606460165340fde4016c29127a143694e884116fc98d2607d64995de87434072dc8c7b8130360380a08afa10c9c0281c02f94149a01444c0b3f21deee16c50894fe0e74813e602e7ea05e7c1ab8a073b01f690896001181409e4a0cdde197c41f4ec1394e1d9ca4b2b69911800042091a80de848b88e0d8a0039641643c1c96a131e69d43a885461bb548df7e0d2361122a8c3b80d862040280e13a1ce6809af205afa0ec86137fa8633e1cf9811a281ed0c1501805d5a1f3861ba9615084072f60bfb88a2b80e77c1701c8910c08932173da1a50613a860b88c9b5920df521a34a13cee158c20af801f44c045881054806b7c10c300ef381657a1f05a06b9a1cf7c0f2c01a5c89791a8b3c41333a0e1c20be9097f0a0554a8078608656c58b21e0440739000488046a810b7208d40020d60f1601a37c0368c0bae8972001ad96091420033898d9c09536071c74e8e0026e8191f89ce160a85a0a4ea102321ac5211d5001ee009d1a1307299c820afdc18f041683a0568e121c8093ae1595c00f52147781dd3a0ad6e1cafc19a6609c6c18c7a821880bacc063541637206ab00ec0c808ba08f280331e0cbb20ecf21715610aca1))) else (if i<12 then (if i<10 then (if i<9 then 0x20a090940c4d08c5ac113a0050ac0782c8a4b210f1809a40140e412b429b8b819eb49e94818f98148c21319c1e39a9d29e1d85a157580887c0e22604f3c134668cc66081c810d2a0a7b2031fa0098c10b281680898c1c1c26e01e261c23402050052fa1b16c00bf487e52077f81b2cc09c568cf161df0a12f9c07f2211ed212d4009b488c45e1b01c01e9097582997740d9188e0089951e0bb5c174c60b35c108d60ee041554a1e4a2076360d07a0271014b68104ae06f201a0d41b9d6129fc03e00863c8101d4117781af8686578174b811f4a187e0114561266802850150e81cd820ad54199f61a8ba00bdc8073011a989c10a07ce4032e495bc68e42a138fe1d3688ca46186cc011281523a1cfe80819c1db76878129cab295ece0d20a186280be1e6e9640a06e8706a13c8a126acae77a06bcc17cae050708735e0f0120530817f2e0f6980f73413278024d21baaa2e886098da8e52c8c75c173841687c9792404246193b019d028cc041bf1a9d45a98b3e0bd001487002cc2162ae068e61d4880537e1ee02898120e9de02d9e02af21cb448e09e192080feaa8afd61c87a038ca1b10c1a1f20b26e8afae1e31c1afce0e09e04df80f64401cc406e42009c00c7701d1be8c54216bc219cb08e3be12c7e084d61d55e998ca054fe8e35a00158100e21a4aa1c99e1eec40882098a040ee80114001a2821d91a06c9c8e3ce19fe619da21ca64872f418f30006e41fa7401042156e41381a14d961556e884fe0fed612e8c0fc148b25e184d8959a60fa78159ce14c26176ba20ed0877f40fb8e0d8061f6c20ca9a01fb40e2d40175c85ce8136401442c98d76165ac9a73e14182135bc0532c1d758069f8089861f6f8133c20bde40a7600d5c09b6688af6a046c80ef561a820168ac0dd7e0c2c41b046029481c2ae9780605570044560c3fe113de16658134b4146440aba40d93e12cc6043861cd36041441efbc138bc15b940bcea155040ed7e0028017db21cf0888efc0a9b815bbc119440b8608c7161fb581e80e070e61eca09d90c193940fe54112c48a97614a0608d0c04bb0153881b82e07e1a110168966a8cb1c02da6126980a69e123ee196fe14da216fca963a003cc295af80e3ce0769e0356c1166c096de0d730153700958c182a60599c15bec015e61dc708ea5c05e3814aea1f25897d1c05e841d1f0139181e0d00831c11e2e17e58101827f4d4066421c8521bad08c3f20e7cc063f49707a066028a8561fc421f87600fda1432802cb21285416cce0563816d909d1ae0a96a0e8a8167f0027f809a3e11df806cbe1bdd889a484e97008f6c15e06110e010bb2073169ae4a1a5721694e060a495aca124a20431286fee8943806fa48e16c146ca013ec1e7c0979840d5f40d8461ba6e123ae1034803bf4120b20bc741046c05f2a0e2bc071 else 0xa72151b40d8f41c1a41618813ea41e6581c3860395e14cd81bc320d05c1e8ec08a720759887d9a11aa40a5e41c4ec034fc179e813eee0bdbe141ae0f9220f5241f8920d83416fb0120c4135560f56299b001d6bc8bb4a98b5a9c65c9b0161b3b60f880880141a9b8107d00132804a6499b7803fca10bd603f2097c040633a0faba1a81a9d1308f0e41008eae82e052820c2fe0daaa117e81ee200a03e1271c16edc0cbd405838197420fa14076c20a1ce02b9a032a80a6061901216c3a0c19614f600d1261f8e004ed218d5e10d4c1f2e29c3d01c1f804ee41571a094e4081fa09f20074dc183a0122061d62c142da0b5228a2421efc407cbe8803815eec9bc5409bc8898e800cae15cae02bc812620192240e0d217c58188780e9700ba009f86c0eb9a067241430e018f01f3280ad160371417fda1f2c81ec100344a01f1c0c9520f30099cda0cd9c05c380e2080caea144ec021400ee208a7c40fbb00617e888408ce8a10f8e0e3688b1781e8ba9a6221ae461bb201e5040b9c2097000e5441d4e0196cc992cc007a41638e13a34006c21767c00d100fdc8180aa0f1f2071bc07fba1552c0f3ea08f921c1541499a0f6a8099580cbfe910dc0781814bdc13500152b40ff769adf4050408ca88102de06b1c979aa862364e5fe03e401bf3811cc61f9ba04cd21eb5c124701b61211336089ba138cc079660d9f017f700224a0e2e0163fe0eda41e3c4860981e67210f6e01290887221b37e0940412f6c1c3a40fd529b9120aab6141549a2c40d6220f7041f4134e84a146ec12fd00302a967b60d616100201c75c1217e1988298ffe883521c7301706c18272869ac07e421afba087c88eb840d0e0670da195701874808b8605aca00de81f4ba03bac107680ae1e075520687a03c260fb461b69c18c20051c40349c170461d14211c24072a4177161dd721998012b2e961481bd821976c02e760a446079440130e097300a56211b4004cec142a41c672086ba1198e0318c0192c0bd72145ec95e800c1420984487a608744487d6c17d2e1c45e0767c1663c169ca89e9819f3e0cf8a9593a9bb060aade1289c888f81e96014e4202c0c8c92a0937208ee6881641dbee1e27a026cc15b3e027dc997d211e9c9d0f009ffe806fc0dede0e65c188a4142180add80f9c01b7569627815d528eb1411da2041840274014d1800fa60c7a29800c89d9e9802a8c7309c3ec1d41c0cab60db1eee5a81742c0b9a805c7016700187bc0157a1b1a216d2a12d241c5781cbacae876091840b8e49a5521425802a7211aec139fe1944400ae4074201ca0a163de0057c964aa187861cfd41d2ae004c61e2f60fad214ada116ce07f58041020da780b59e141e012bca0e4d21e1cc02132ee8a41627aff7de1902e0ebf20879c0e28a0d89c883dc110769474a1e6b4135621cb70) else (if i<11 then 0xa122320af1285c840f9a01ce1412ad60a83a0c3dc085b810fd6037de8a02611ad6002ce115660f8ea05e1a15f1806714139b604e741d9f0092669c38a1a96006cce1de56821ea9adc60a72609fac01b941a5a686a8215a2207f62067f80e3421d4c49d0b888a82176d807364178988c4c81297e093901dade0386a8e7e2035460a8ae1a01e1c3ee9adb4067481f11e0367207916140301ec3e8856c89eb608d3403e768cf5804b4e8c9f08b046995400e57400c60148521c0cc14fd40045a8cade063ae8eb4a0ac6e8f0ca0218a0c27009e900e072962d289aa00b5761b946171da0da8e0588c892cc00f8c0f6fe1446e190f4097b80ade2082861cbc6185b81d01613086083aa17fb60d1b200630899020509a1610217c9217bde960e0136e8180160cffe8e8440515208ea81b5f49913e180ec0b9661c36eeea921a9101c5860f81e18cee0e25e9c4760bc1c106fc86b10088c89b3d218eba14c64193d09d25204e9689dec86346874980265a1044e14f0211c640fa2e09b920da1e152fe14054156b218df4ffa880c1628993e8a8b4883e61f6a817cfa1e4c41835a1876c0252c0c738048700ca6c1a4020c6f80b6780c65c0f33e0ac8a1811095ea004e141e09a1ece887f040c10e0bcac0c0d41b534999c01cab217ec002baa8e03812da8064e416c8c0e05c138460ccd01a52688c4413da2c0ffc10e5605c500cfb00852a01ba01a4d2010701abd00bbf61b7e8092d20cb2e861568e564873300a1301f7bc09c920a35001d8410ed21e6e29c67214bae15e9c897a099598089e0055ea05470879ba85da805f9e1cc481acf496f8c163109aaba8815203ec61b2181961e0e67e18e541951414d6e0d9520eea28acbe1ce2405a268e9460c7141a99e1126089028986441d39c03eb00c1f0165c20362a0cf226eb8a0e46a0c2501667006a1e8b936197e206a58023da1b5bc8ac9a118aa1257a101a200e6216d5819b960ec7e0d592125820e5b40621815a5603c121202a1e9d40481c036f2101f6189ab2ef5e08b7a11a5a16b521889015cd21822215cf609c380f5d812a141a718131ba1df5200a669a8c605014120901b51a13fe21d214073c4874d41d7b40751618386076fa140a80c1c29c5700727698992051ac005021aed0056de00a381f65689a9e9ab321ee940e9ae13d081ef4202ea0005e48e18017b3217b540c4b802b60189900901e8c16289b621a1680254a10dd01ac1c184280ef180c82287c441905e121341ad5203e3019ab41cdcc010f4166d48755a4eae212726117a89c970154b00a9308dc34049901f84a97eb606d24095ae1db441a8968cc2011d349b3ee0a2949ac0a1f18e975e202d4a147040d37808b5a181580b3268e4500f8d20f3960bf3e19a80047be00cde0422c19ed01cbf8081a41e7a011e4618ac00278c0f0a805 else 0xaf7c069b00495a16150150761d3d487ad8145c215796013c6156909ceba89db61229612614187240412c02c9e97be4136121c7941b2f40a31089f5204abc97ce0038bc0aea00a3e009e3a958da9118805bf69ebb207158042f01faa403a8a057a81764219c9c1109a9f19a0cd7a100a2897c00ce8219bc00a7d0037b81a95680922164e4053ba8e0de1f5320f8a286a46187cc036de02d128a9c620e149962a1ea9e02092008d60fcb00cc5c0fe8c1251c02a5817a4209a86162e413ed409fca0f3c49ec4a1ca880229c8807c009008a42812c5c17dc207cd80a0f69a822993c89606a0eaea1cb080f07e1ef2a0405416aba13860090768dfee01e1c140da1d3469b3a68a1280bf421071a16b821de020bd940ff021d11210a3617b1411fe60d9bc1b9f418cce8ca621c9b8064d80ca141f4da11156987169e82600b4e973ec11d7297b48112089f8e20b9f0044d218a7a131c01e8860cb0210eea0d54c1981686dc2991e216daa007c41c610010a01b0d40fb3488f200f7ea0f49e0cfd6008e61b3341a2a20613615e760954e026ba0bf8488b0400d9a01d001fae60b6501d26a147da9c12e1d026153da0203a978c21db361f4749b310038f60fc960e1e0029240da320dff21ea16098fe000f210ea4111aa0dc800ebae97646169300258e1bd2814ef6030f88897a17aae175069f7c499a1e0a4600ab508aac8132dc1602a03118189da0e5921aad410e088963c9f596109ea18290191c08c33809336880ca009fa982161818a1624c09f40177401d82a03b9c1b1440388c1ba44094ce1e91a1b2be1fbb61ccfe0a6e01ad7211e6014b3e0a54e152041745411622975a30201605b941da500e92e0bb7a05fc41bd769c202172e001d209c49013c7c07d1807a0418fd8110a61f13e0c12604a8007bc4170fc11558082261f8de1ec6e1dba2059be086901349a0c0b40a5d89bae60409a0dc68976701439c10a640273619f5c0fd141ae660c0ee03844063d6178ce12c840e5300c6c80118412546189480acbc1373403bc20dbb61641c0bc4004424133a4084181c63c0d114108621359c0187609d9a00ff403d5486e30170d80af2c04c9a1978416a261606e02a2213de60662004b360296c0220c96122114f60b5e60cb7216e3c1ad189ef5e1be100690a14fe81e5b01edcc1f9420dee8147560911e008000f59e1a6f419e66096161401a8d7e2894c802f429e7b800a9414220199a41d28c154161f92c1f9ee01506976228b8701d08604f9e0a380144da006888a1820e6360ffca07ecc1f5ae05bca0a42a0c532084a003f0a2e7880e1aa1a7c897d5c0f3b40d8dc8419c0db341d96e05ce60c038057fa97aa8151e41f0fa12522069668973c14c0c184968e8a08b8400c544102861bb720009a118ea013481061c0496a8a8c608a0a9a2f811c9e05aa)) else (if i<14 then (if i<13 then 0xa0104e21762c9c6ac0b2be158e408a261fb0a1f77e1f8a41c6821e74601c5a19d340ce1c043e6049ea1acc4093129aeb4030c002dde06e1a095f00143c0ecb60a2ae18200056fe024888a9e6011be061c80ef6087cc00c01211c0486d540b99618b348e9e4078680328a95f70002301466a0e03687d3a09ba615f6c9b2901eff81234a8a1ce145061089c0c89810a560880e0b85e097e20eed609c0015fe608778069300f41499bae14de2177ee0a0480f4ba160848c47c9c4ae04776059d007a5c04d541c014ff7060b824172a80b44a6f1c0ae7840e872199660685a14e2a1e5dc1c9f2171e29c60e0161e1b3fa030be03abe18a9a1892c88ffa1dbcc9a310112f01eb90122b210f3a0dc2401ace1709a01cfe13366017941e446860c48c28a164c61bd1c88e040708a09db8052de0575897eca0f34806ef0123968c3da9cada0c5e01f1f686f1c8a89c1478c1d53289b0c183d81d92c10aa204d6c0d6d201a3a9724a955da1295e1fbe20fc26145868779c1c4688da169e7d61e0101f91400e90179d812c2a895f286ca81ab521299a1497e173bc0041c014b403ad819d9e0147095c048a26c07238092e018b5a1a2121e72895976062f0125fe02fde0aec219dee0dc4e2e7d4041c21fa2207dfe1e33a1286e17ae217c601f554052621aa8016e9a10a801a76c1a5fe1fb940df240077c0aae01e9a4119668aae40fcda0f0448c5c2035be017c29be601de9e1861e0eaaa16f040855a121400c3660d1460a24e195f001dcc10de28b8f8ae84c05dd41adb61ad3a1b6d612f1a1b90a18b941beb81a3921b776196b8083ca191bc805660d512195209b8c2097c0127b4078869c43c0b46c040b81d684961e61c16603fa6047861f092085cc0d30c15b7e8bc501dae016aee886da1dd06040f001b0c996d289ef21c5c36e88a030620092e13b3a041fa1311419b540eac61b93c9be148c4f01f83619e101033a160e8025120247e0891a090f80e300110d8128c81139c0493000526003b60593a0734e16bfe021dc100c61c2820451208c94840fc08cce1a7a68a05089c320ecda070da08dee0f47817f4289ddc005ae0fb18893ce0602c1845a04c7e8c4821f7141317e1d6d01f15816ff41416c13ad68703e13caa1a8461d4a41e47400dd814c960b3041170a18f6210126130e20c7f04ec3e1cc121e18c1227a0c3460543086b2c0e3249b19a07c0e126d816ef898c5c8af8402ef40339c0981e08c121af3017b6c0f5b2058c80152e1f98c859b215334035d000198173f605b321d9bc869969a5ca1179617e8c0a202962e60e4520268a086ca1924a98468157dc0cf5e140668601608caa15c04883a20669e1b4e69990e06c7c06c42099c41589017a928851a024261e29c0b950198aa12b149b82c195840c4481855c01ec41a324870060b51095f5c1 else 0x108fa8dc761d784106b812a84017aa19b2a8caa01881812b7e09f7801a4012010096a81a0ae03592195a41ac6a0f84e05c921f6200ed5602e22881081d8dc13b9017ee0039b6186ae026768c608887f4157268c3909ede286b5698c30133f0959148c5e00313804bcc0436c8dda21e77207eb813f92021e0012ca0462e1a9f01a1da13fda0925a16b7a4e6b802d761abbc8b9ea1ef9001c841188e0efa41c6f01112a884780261604a0616eb49aac49d07801b7a0c2b61c7b087f6c08b309dc7e1ed7e8a7fe8610c122e416c000dcce153b01758c09b70093f407aaa077000b78e19a46165f69b69418e061325e18d1e115861678899b5210e869f910880f01b45a14896103e60dcec08e061f7d81d1de07e32088e01d5e60c3261224a10b040895e18b741b72212d6008e408b0e6067ac08bfe02c561c0b2161fa1ce9886690174820f22a8f19e02f1e140900753406f4401b221fa029c3a61be5e0b2401031c01800095700775e0a6c80c0661d2da15a7689042017660fc46911c41146487bb011ef21716208c74008369be5e0acda07b2e9a5061676c028d41a4f6078d88613e0cc8417e6a0a10e86c741dfd8125c6180da8c35e1f034996b01955a1d5d29d1fa1bc4603ffc13f161f3b20ec5c89b320432e0ee40025d613aa2190889748c07ef29b1fe003fa9ebfa18e9c0a53e0b36c1e3f810b929581e03b2e13f7003a661483e012e612dc41ebea1bc601d6e60720218fec1da3e18ab499cee0962c0c1bc0f02a1c5481a8f601eac11b2c1f17c047e8091780b2000680e0ce469c51c06ece87fe81ccce98d4c06fe40affe1af520d49a88d56889be87b641549e1ab1298f581809c192f005efc0d57888af2066b21aff8119ac0f7861010a159b48739a1fcde02ce40de2412a2a1ba1af72921b0f0161c21502296dae9b9c497bc6061808624a1ed4e9ed961c64e17c160fe020966a0327c065f614cf207d2c13f4e0025089564115ec1211c977e80f28a1a08e1933e0d65e08f060b4b40f27c1734c10214154da03f7817cce08590046140454e028e8151d01b198094940fa8889414994ac0f1241ded8053f00b4ee8e5ac07a3408e7c1e5fe89bb6177841bb8407e8c0b23c1b9a813e100df120cf7a1ae840f96e96dcc6eaea07f8c080aa029d215d9a1015488cf205cda03cee18a3a89c988c18697d280573a06d0804fd00360e0e3801f002008b4082cc14f9610c5c97c629652a1df78175ba7f78a0e84803a4a06ebc0350601a840110295bb40c04a00106981fa06be60793e095c80a5ae17d600e50a9a3ce02ed2820080d2d61aa681fb300086017ba89bbac05d881e3be0471c0b54c1cd1a078ae96624190b409cec15e4613a4404a3c1153617c368982203df8149d21b4000657e977489b36400d5e0fe760510216a701947489e0404c120c6) else (if i<15 then 0xac21e2ca1741a1864c0121817f8e98df41a1868f0ba105c2058e6804320f86a0c6241a5880fa50112908dd2a0282819e2014abc115d80b004062241ed8c067c810bf20eb3e15666958fc0e15c153fa1e58c1eaa81b4a41f3d88883c041ac8747219cc4199260e6d8020e48efca02b5a1bbdc0a2fa15346077da15b1a1968c01ff49eb8415bd6002e28950013c1818d9c128a20f21299b980ab2a88f6e0c8540c284136360fd8c05408155ea164aa1eef20061a0b7a219fc60ae6409dea039f89ce8402d201581889f2e0698400d221890c1330017e0410fb68731e033ca06ad00b2e89c55c98e520c5be0cecc1e1240467c00ec21c20e1655897e4207fcc1526e1c1d80a2ca8dce610d7e07afc03f5089af20aeea00da816298157e216a0000ee60f0821369a1787e0cc1e150a210692193060ce221660a11a6a1174c03a08034029c4520bd420ce7c886821f978022740e48808fda174761bdbc014e28f0660b6fc1634e17a3c8c2ba1b35804dba0a88e8c79a0fef20be420a9d006e2a1d04e042b4087b6006b20f4e418ec81c3100ae3612dfc044f81c9349a6ba1a4201b4d018a001d9500dd2015ec61aafa07a8497a5412ca201628898801ee70160a21710802c6c11180077ba8e55c1b1e81cfba114c404ac21292618f4c1cd6c1ca381d7f61761206f921a550050f81918e0e7aa0bec01f0c40d6b011c4804d1a1fc3216dfc9abaa1eb7286eca174ea059ee013680f1501b6781bfdc0cd56964501be24026280ffb01b58c1973c113f41af121b022069c48c3608954c0947e166be177da06f1e1c11008164109921c4ba02e060c978149ee8ea241e1be1e42e1164c167ce9c2c803b621353c0b02212e741377a0f4529737c1a25c1cb9487ce218dd2075f01d8860a4ac0ddf28ac06130d418a548c7cc12e181aeb61f43c15864115ae1910c075d219c041bfe6188f01c902102aa0edc41669685df0185f69f42e89bf80d2689a3ba119f80adb808e3a004669a29c0cf0203b14892901a6ac00b040d4c8137b215c90147a816e401eafa023b81b46c15ae60df7e873a80d96c9a53a005de8b9040ba4e1d166012b21085007bee08b0c1c8e0098a0137c4100460a7fa1280685caa8705015f4c191720702a87aaa1b7da0b92a05dbc062da8c4a41392c1c1920de1687f2409cd807c3e08094049a0175f40658e048b49a5ac1d0ee88ac4011c01d5a40ed3e1e36603046966561b97613d361645e0d32e12aa4189f80711eee8200ae4a1fa4e0d44c06ce29c69c031c208a4a00f2c0f0cc0aa9c986640f0f81832c1441c86e04091e614b1c15422125b219e408bc6e180461984219916182da06d8002c228e40e18e3e007540e1921d18c0e9401236804be087e36163260746a09be015988103ac0a180000100198818bc81e8c21a86a0c6949a04202a12 else (if i<16 then 0xe07ba218cae10fee1fc741cc2e191384e60016ace0983e0811c1b7b809b221ac92024e00832c08dcc1da14045a2007901971a126f8061440873d4e8ac02ab00e81c1a6c81f0b612ffa031540188204a541ed3e1f808991c80cb889ab4e0d3c617028046449a11a13b48150cc0ceb81050a95ffc03c6a0f9480627c016928975c1e11e181681ebd807b5e1219a17132053541be6096c561518215ab2033ae1056401d64167aadf5ea08bd60378e0a32605248000a40ab6a134500f55a0df9402008065de078e20e1041e61a070b68812c143d0082e89b85e01da4106764eac409a7e0ed98137481339201e728e6aa13e4218d2205b0614a94982621c242060421b5da0ba200776c97a2406bb209edc970ee1452e881fa1473403e841081e0103e0c9e60636c1dfba0bd2c01542062a012cea003641e6d21bdf09ab121b13a0b6208d100168d600b8404b9c0ca201ab641ac369d27e85fd20c87a120f80aa1c198761cee803d64109249123a9628686c3205488d10d69c2a01e9f4181a20db6c06da411eb81037c0b4da1de2a04b1a0e8f411b1a1291a1adfe029bc090b2132e60f7c0980ac129a21b88a0902619c6e0cdb81d3ea997301b2860d982863101d8ee05f5611e101c4220468e0c092065200c5980c4f2015b49a6960798a019fe0e9f0059661e85a1dc28988101c6cc9b99c0beba13b7812e2e1a63c0f50e04f7414d5a1cc78042c21f076045f21074e14a440149e1da64046f0160521cf2816e6e074f803c960c99001f8c979760426416f48018d210d1813c22155928736e194b60ab98805c00447c09f969c232899ae045dc0a41c8e62c1f5d80644616f368b09e1812a0f1d608c5816f729a9aa007e00986e012561389c0abc2128e00b0840333609d740ea4a898a80efec1cea00b7f01a6861426614f4a20f6005d021b26c0e0081bb1a15d2c058508b1f687c2a13cc206c0a0e7300576a151369a4ce139dc155c815c7200728123189a582159f80aa6c13d480013615fb6146b611b741c52804afa182509a65e112460c8b6175ce1b64a1454c1601a148b21dea80483015da41753811ce089c5a1c9d00998c6f2de1cde6841a41c0660b15601a7614b4c0a3a600cec0d1640d4bc80a3c021681df8011fba19dca8785005a98121f49787a0007a1c080087520ad900fc6e1784c094a6014048ce4c05e40145a81794e0996c05ea00643e05b6e86ace0002419ef01792e199c88aa060cc2a0c9b60fdbe00aaa8b1ae096f407b6a1bc041ae2607b1c074821d30200e048af581091e1564e1cc9c15ad48e7be014d61ec908cc5818c020b70809dde0ab1602a8e960861d43e044bc0a70e9457c099e601a061dde81312c19e88083e212bae1c41e98f321d6000fe3817308998960301a9e410152de0be22966bc0e4e20ff22033f60f43a19d6419 else 0x180a4c4124e207288085760e6aa9625019072084f419b6886be60bee811f8215e3a1a222c00c2010840070c1e2040d76a16508859f)))))
def oH10 (h : Nat) : Option (Nat × Nat):=lookupWord 2481 4962 13 20 12 4 oH10F h
def oP11F (i : Nat) : Nat:=(if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x69c914832feca34e48a41b5f955a724520cbfb2ad39229065fc9869c914826ff5db4e48a41bf9485a724520f7ca43441229073f591a20914835f6d151048a41adf6968824520d5fb4d441229069fda7a20914825fedd51048a41cfd6059824520afeb62cc1229067eda2660914833bed2b3048a419bf6999824520cbfb4ecc122906bee226a0914835f6a135048a41afb549a824520d6fcaad41229063fd956a0914834ff3bb5048a418ff65da824520c7f972d4122904bfebb6a0914831fe4c35048a418ff661a824520efca434c9229067eda2a64914833bed2d3248a419bf69a9924520cbfb4f4c9229063fda8a64914823fedd53248a415fb2e52126120cfe922d09309047fcb968498482bf65caa44c24157f2dd9526120cef92ad29309073f611660984831fed0b304c241cfb8899826120e6fcaacc1309071fe77660984829ff5db304c2411ff6ea9926120bfb57698126906df9a75c093483fe89842249a41bfc6821124d20ff926090926906fe9a0484934833fcd012249a415fe6c09124d20afdb64489269057ddb324493482bdeda12249a415df6d49124d20adfb6c489269055fdb7244934829fedc12249a419fe6819124d20dfb260d0926904ff9b0684934837f290b4249a419fd245a124d208ff972d09269047fdb968493483fe49844449a41ff24c15224d20dfd340a91269077da0064c93483becb832649a41df58459324d20cfbb42c99269077ce2264c93482bef5db2649a41fd64c25524d20def3412a92690775d9395493482bf6d912a49a4197f69c9524d20cff340ca9269055fcb7654934837ec9834a49a41bdb549a524d20cef92ad29269047fcb9694934823fedcb4a49a41fb64c26624d20ddf341331269076dd93998934833fcd032c49a415fd2c59624d20ddf400d3126906ef9106989348377cb834c49a41bbd845a624d20ddda42d31269066fc916989348337ec8b4c49a41bbb889a624d20dddaa4d3126906e7e556989348337e4ab4c49a419bf655a624d20cdf930d31269066fcb96989348277f5db4c49a419bf659a624d20fbb2613b9269075dd939dc9348367ed34ee49a41df64c19724d20cdfb4ccb9269065fda765c934836fd0034e49a41b7e441a724d20dbec22d3926906ded2169c934832fe48b4e49a4197f645a724d20dbdc44d3926906ddd3269c934836f6a934e49a41b7b2c9a724d20dafcaad39269065fd9569c9348367f3334e49a4197f659a724d20cbf930d3926904dfebb69c93483dec9851049a41afe6828824d20e7bb2744126906afda6a20934834fed3d1049a419fe6819824d20cdfb4ccc1269065fda7660934831fe4c35049a411ff2e5a824d208ffb72d41269077d930a64934833fcd053249a419bf69a9924d20cbfb4f4c9269047fdbaa64934837b88834a48a41b79485a724520 else 0x415ff6d59824d20edfccccc1269067fda666093482bfedb33049a41d7f9dd9824d20cffb4ecc1269057fdb7660934839ff4433049a415ffaed9824d20ffb260cc126906ff9a066093483beec9b3049a41bbf6999824d20dbfb4ecc126906ffa006a0934837fc8835049a41bfe5c1a824d209ffb60d4126906ff6116a0934837f690b5049a41aff605a824d20cff922d41269067fd916a0934827fed8b5049a41bfb889a824d20dfdaa4d4126906bfd826a0934827fed935049a41bdf955a824d20d7fb0ad41269067fc956a0934833fecab5049a413ff2d5a824d209ffb6ad4126906efe666a0934833fecb35049a413ff6d9a824d20dbfceed41269067fd976a0934827fedbb5049a41affa21a824d20cffb72d4126904ffdb96a0934827ff5db5049a41dfb54a9924d20eefcab4c9269067fda5a6493482bfe5ad3249a41dbf99a9924d20cffb4d4c9269073fe88a64934833fed453249a415ff2e29924d209fdd7690926906ff110544934823ff5db2249a41bfa4415224d20dfd260a9126906fe611548934837b6a8aa449a413fbaed5224d20dedaa4a9926906f7910954934837bc984aa49a41bdd8465524d20deda432a92690677d91954934837af19caa49a419fd8459524d20cefaa2ca9269047fdb1654934833ef19b2a49a411ff6cd9524d208ffd76ca926906bf611a20934835f690d1049a418ff6468824d20d7daa544126906b7e55a20934831fecad1049a419fb5499824d20cefcaacc1269047fdb5660934823ff5db3049a419fd8469924d20cfda434c9269067ed52a64934833bf2ad3249a418ffa229924d20bfcd76909229057f6bb64491483ff08844448a41df96462224520ffc220a1122906fe9a0508914837d6d228448a41ff84415224520dfd340a91229077e59154891483fb8884aa48a41bde6825524520feca432a92290777591954914837b6d14aa48a413df6ea5524520efe220ca9229067f9a065491483bf290b2a48a419fb6899524520abf96eca922906f7a00694914837ba8834a48a41bde4c1a524520def2e0d2922906f7581694914837b71134a48a41bdb509a524520dedb64d2922906f5e33694914833bec9b4a48a419df261a524520cef972d2922904f7ebb694914837f88834a48a41bdb549a5245209fdb64d292290677d956949148377ac0b4c48a41bbb889a624520ddda84d3122906eed526989148373f2ab4c48a419bf655a624520cdf930d3122907df1109dc91483ef290cee48a41d7d6467724520dbdb453b922906ddda39dc914836bed2cee48a41b3f69a7724520cfdb44cb9229067dda365c914833bed2b2e48a419bf6999724520cbfb4ecb922906dfa0069c914836fc9834e48a41b7d485a724520dbdc44d3922906ded4269c914836f6a934e48a41b778cda724520cbfb26d3922906dbe44) else (if i<3 then 0xc2cb1269067fda165893483bfa58b2c49a415ff6c59624d20efdc44cb1269077dd3265893483bf6a932c49a419ff6899624d20eefcaacb1269076fd65658934833fed2b2c49a415ff2d59624d20affb6acb1269057febb65893483fec9832c49a41bfe6819624d20efbb26cb126906efd506989348377ec034c49a41bbf6c1a624d20ddfaa2d3126906efd716989348377ec0b4c49a41bbf6c5a624d20ddfaa4d3126906efd826989348377ed934c49a41bbf955a624d20ddfaead3126906efc856989348377ec2b4c49a41bbf655a624d20ddf96ad3126906efdb56989348377edbb4c49a41bbf2e1a624d20ddfb70d3126906efebb698934837fd0034c49a41bfe441a624d20ddfac0d3126906ff970698934827fed834c49a41bfd845a624d20dfda42d3126906efd61698934833fec8b4c49a413ff6c5a624d20dfdc44d3126906fed526989348377eb134c49a413ff6c9a624d20defcaad3126906efd65698934833fe4ab4c49a419ff655a624d209ff96ad3126904ffdb56989348377ebb34c49a41bbf619a624d20ddfb2cd3126904ffdb7698934827ff5db4c49a41f7e4427724d20fbec233b926907ded219dc93483afec8cee49a41b7f6867724d20fbdaa53b926907d7e559dc93483afecacee49a41b7f6967724d20f9fccd3b9269075fd969dc934836fed34ee49a41ff64c18724d20efbb26c3926906efda661c934836fed3b0e49a41dfd8459724d20ebfae2cb9269067fda165c93482bfed8b2e49a41dfb5499724d20eefcaacb9269067fda565c93482bfedab2e49a41dbf9999724d20cffb4ccb9269057fdb665c934836fea834e49a41b7f581a724d20dbfb00d3926906dfd5169c934836feb0b4e49a41b7f605a724d20dbfac4d3926906dfd8269c934836feb2b4e49a41b7f615a724d20dbfb2ad3926906dfd8669c934836fecb34e49a41bfe441a724d20dfec22d3926906fed2169c934833fec8b4e49a41bbf999a724d20cffb2cd3926907bfa00a2093483dfc8851049a41ef74c28824d20f7f2e144126906bfda0a2093483dfb08d1049a41efb4868824d20e7f923441269073fd91a20934835fed0d1049a41efb88a8824d20f7ba6544126907bed52a20934835fed151049a41ef764e8824d20f6fcab441269073fc95a20934839fecad1049a41aff6968824d20f5fccd441269073fd96a20934835fed351049a41e7f9de8824d20e7fb2f44126906bfda7a20934839fe5cd1049a41ff64c28824d20dff341441269077dd93a209348377ed351049a41b7f69e8824d20aff973441269077fa0066093483bee9833049a419ff6819824d20efec22cc1269073fd81660934833fed0b3049a415ff6c59824d20efdc44cc1269077dd3266093483bf6a933049a419ff6899824d20eefcaacc1269067fda566093482bfe5ab3049a else (if i<4 then 0x3483fec982a449a41ff34c95224d20dfdb44a9126906dfda754893482bfedcaa449a41ff64c16224d20ffb260c1126907fcd32608934837f6d130449a415ff6e58224d20efbaa0c99269077dd6064c93483beec032649a41df75459324d20efbac2c99269077dd7164c93483beec0b2649a41df76c59324d20efbaa4c99269077dd6264c93483beec132649a41df72d59324d20efbb6ac99269077ddb664c93483beedbb2649a41df72e19324d20efbb70c99269077debb64c93483fe6a932649a417f7aed9324d20fef4012a926907f791095493483fae984aa49a41fde5c25524d20defb412a926907f761195493483fb690caa49a41ddf2465524d20eefb232a926906f7da195493483fb7114aa49a41fd74ca5524d20defb452a926907f6cb295493483faec9caa49a41bdf69e5524d20eef9312a92690777cb995493483fec984aa49a41bfe6825524d20fedaa52a926905fecb295493483beec9caa49a41b7f69e5524d20aff9732a926907fd930594934837fcd02ca49a41df764d6524d20aff972b2926907fd9305d493483efcb82ea49a41fdb5497524d20efbb26ba926906dfda75d493483fec9810a49a41bfe6808524d20bff36042926905ff5b121493482ff6d910a49a41df764c8524d20bfbb6642926905fbdb421493482f7edb10a49a41b7f69c8524d20bbfb6e429269057fdb9214934827fedd10a49a41ff64c18524d20dff340c29269077dd9361493482bfe5cb0a49a41dfe8019524d20efba60ca9269077f970654934833fed032a49a41dfd8459524d20eefaa2ca9269067fda165493482bfed8b2a49a41dfb8899524d20efba64ca9269067fda265493483bbf2ab2a49a419ff69d9524d20ebf96eca9269057fcb865493482bff5db2a49a41ff64c19524d20dff340ca9269077dd93654934837fd0034a49a41bfe441a524d20dfba60d2926906ff970694934827fed834a49a41bfd845a524d20dfda42d2926906f7d51694934833fe48b4a49a419ff645a524d209ffb62d2926906fee22694934837f6a934a49a41bdf549a524d209ffb64d2926906f7e55694934837bec2b4a49a413ff6dda524d20cff930d2926904ffcb8694934833fe5cb4a49a419ff6e5a524d209ffb72d2926904ffebb69493483f7d004cc49a41fbe4426624d20fdba6133126907ef9709989348377ed04cc49a41fbd8466624d20fdda43331269076fd919989348377ed0ccc49a41fbb88a6624d20fdba6533126907eed529989348377ed14cc49a41fb764e6624d20fcfcab331269076fc9599893483b7ecaccc49a41bbf6966624d20ffb260bb1269077dd935d8934836fed3aec49a41ff64c18624d20dff340c31269077dd9361893483bfd0032c49a41dfe4419624d20efba60cb1269067fda065893483bfb08b2c49a41dfb4859624d20edfa else 0xe5c19526120e7fb00ca9309067fda065498483bfb08b2a4c241ddf5459526120cffb42ca9309057fdb165498483bf71132a4c241cff6099526120cffb44ca9309077de3365498482bfe59b2a4c2415ff6cd9526120eefcaaca9309067fda765498483afe5bb2a4c2415ffaed9526120dff400d2930906ff910694984837fc9834a4c241bfe5c1a526120d7fb00d2930904ffdb0694984837fb08b4a4c241bfb485a526120defaa2d29309067fc91694984833fec8b4a4c2413ff6c5a526120dfdc44d2930906fed42694984837f6a934a4c2413ff6c9a526120dfbc66d2930906f7d53694984833fe49b4a4c2419ff64da5261209ff966d2930904ffdb3694984827feda34a4c241bdf955a5261209ffb6ed29309067fdb9694984827ff5db4a4c241f7e4427726120fbf2613b930907df6119dc98483ef690cee4c241d7f6467726120dbfb433b930907ded429dc98483ef6a94ee4c241f778ce7726120ebfb273b930906dfda39dc98483edf224ee4c241f5f9567726120ebfb2b3b930906dfda59dc98483bfb08b2e4c241d7f5c59726120cffb42cb9309057fdb165c98483bf6a932e4c241df78cd9726120ebfae6cb9309067fda365c98482bfed9b2e4c241def9119726120affb68cb93090777e5565c984833fed2b2e4c2415ff6d59726120dff220d3930906ff93069c984837fb08b4e4c241bfb485a726120cffb22d3930906fed4269c984837ef19b4e4c2419ff64da726120df7c88d39309067fd9469c984839fea8b304c241cff5c59826120e7fb62cc1309073fd32660984839fea93304c241cff14d9826120e7faa6cc1309073fd54660984839feba3304c241cff9559826120e7faeacc1309073fcb5660984839fedab304c241cff6dd9826120e7fd76cc130907bed5266098483dbf2ab304c241cff6559826120b7fd76cc1309077ed52a6498483bbf2ad324c2419ff6969926120aff96b4c930907fd9b14c093483fecdaa6049a41ff66d93024d20ffb36e98126907fd9b84c093483fec982a049a41bfe6815024d20ffb260b0126906ff9a058093483fec9830049a41bfe6818024d20ffe2e108926907fe97048493483ff8882a249a41ff64c15124d20dff340a8926907fd930584934837fcd02c249a41ff64c17124d20fbf2e0b8926905ff9b05c493483ff290ae249a41b7f69d7124d20ffb260c0926906ff9a060493482f7e5b30249a41dfd6049124d20affb6a489269057fdb8244934837fcb834249a41bfd545a124d20dfeb02d0926904ffdb768493483ff5002a449a41ffa4415224d20ff9a60a9126907fe970548934837f6d02a449a41ffa2c15224d20ffcc22a9126907f6d5154893483bf648aa449a41bfb6855224d20bfdb62a9126906feda754893483ef65baa449a41dfb2e55224d20dfdb74a9126905feebb5489))) else (if i<8 then (if i<6 then 0x922907bf521a2091483dfac8d1048a41efb88a8824520f7da8544122907bed52a20914835fed151048a41edf9568824520e7fb2b44122906bfda5a2091483cff3bd1048a41cff65e8824520d7fb4f441229073fcb9a2091483ff290d1048a41efd6068824520efeb2344122906feda2a20914837bed2d1048a41bbf69a8824520dbfb4f441229057fcb9a2091483bfa90b3048a41dfd6059824520efeb62cc1229077ee2266091483bf6a933048a419ff6899824520eefcaacc1229067fda566091482bfe5ab3048a415ff6d59824520ebfceecc1229067fda766091482bfedbb3048a41cffa219824520affd76cc122907fe52166091483dfac0b3048a41dfd6459824520bfeb62cc122906feda2660914837bed2b3048a41bbf6999824520dbfb4ecc122906bfd326a0914835fea935048a41aff6c9a824520d7f8a6d4122906bfd536a0914835feaa35048a41aff5d1a824520d7fcaad4122906bfd756a0914835fecab5048a41aff2d5a824520d7fb6ad4122906bfdb76a0914835ff5db5048a41bfb889a824520dfda84d4122906fed526a0914835fec135048a413ff6c9a824520defcaad4122906bfc856a0914835fec2b5048a419ff655a8245209ff96ad4122904ffdb56a0914836ff3bb5048a41aff61da824520cffb2ed4122904ffdb76a0914835ff4435048a41aff661a824520cffb72d4122904ffebb6a091483bfac0d3248a41dfb54a9924520eefcab4c9229067fda5a6491482bfe5ad3248a41cffa229924520cffb514c9229057fcb8a6491483ff8882a24c241ff94857126120dbfb4eb8930906ff551684984827fedbb424c241bfb6893226120ffd220a1130907fe97050898483ff308a844c241feb5054226120dfdb42a1130905fedb150898483ff5002a44c241ffa4415226120ffd260a9130907fe970548984837f6d02a44c241ffa2c15226120ffcc22a9130907f6d51548984837f6d0aa44c2417fb6c55226120dfdb4ea9130907decb754898483bf65caa44c241bfb6e95226120bfdd76a9130906feda254898482bfedcaa44c241efe4c18226120f7da64c1130907bed5260898482dff5db044c2417fb6c85326120affb7229930904ffdba14c98483fb6a92a64c2415ff2e55326120ff5a84aa130905fedb2550984837ded22a84c241feb50974261209ffb74ba130907f7a0095498483fbc884aa4c241fde4c25526120fef2e12a930907b7d80954984837bed04aa4c241fdd8465526120feda432a93090777c9195498483bbec8caa4c241bdf6865526120fedc452a930907f6d4295498483dbec14aa4c241bdf68a5526120fed9652a930907f5e33954984837bed3caa4c241ddf2e65526120fedaa52a930905fecb295498482bfe5ccaa4c241f7e5c17526120fedaa4ba930906dfda75d498483bfd0032a4c241df else (if i<7 then 0xff29090a48a41dfd6448524520bfeb6242922906feda221491482ff6d910a48a417f76cc8524520bf7b6842922905efdb6214914836fed390a48a4177f6dc8524520affb7242922904ffdba21491483ff88830a48a41bfe6818524520ffca42c29229077f591614914837f6d130a48a415ff2e58524520eff400ca9229077f51065491483bfcb832a48a419ff6819524520efea42ca9229077f58165491483bf71132a48a41dfb5099524520cffb44ca9229077de3365491482bfe59b2a48a415ff6cd9524520eefcaaca9229067fda765491483afe5bb2a48a415ff2e19524520affd76ca922907ff110654914837fcd032a48a41ff94859524520efeb22ca922906feda2654914837be9834a48a41bdf601a524520defb60d2922906f7d32694914837bec134a48a41bdf6c9a524520defc66d2922906f7d43694914837beb9b4a48a41bdf20da524520defb06d2922906f7d93694914837be59b4a48a41bdf6cda524520defae8d2922906f7db4694914837bedbb4a48a41bdf2e1a524520defb70d2922906f7ebb694914837fd0034a48a41bfd441a524520dff260d2922906f7d50694914837fcb834a48a413ff6c1a524520dfeb02d2922906fee22694914837f6a134a48a41bfb549a524520defaa4d2922906fedb2694914827fed934a48a41bf78cda524520def8a6d2922906f7d53694914833fec9b4a48a413ff2cda5245209ffb66d2922906f7d54694914827feda34a48a41bdf955a524520defaead2922906f7c85694914837bec2b4a48a41bdf655a5245209ffb6ed29229067fc98694914827fe5c34a48a419ff6e5a5245209ffd76d2922906efd326989148377ea934c48a41bbf609a624520ddf8a6d3122906efd536989148377eaa34c48a41bbf5d1a624520ddfcaad3122906efd756989148377e42b4c48a41bbf615a624520ddfb2ad3122907df9309dc91483efac0cee48a41f7b50a7724520fbdaa53b922907dde339dc91483afec9cee48a41b7f68e7724520fb7c893b922907d7e559dc91483afecacee48a41b7f6967724520ffe220c3922907fe52161c91483bfac8b0e48a41bfb6898724520dfbb46c3922906f7da561c9148377ed330e48a41b7f69d8724520eff260cb9229077f58165c91483bf6a932e48a41df78cd9724520ebfae6cb9229067fda365c91482bfed9b2e48a41def9119724520affb68cb92290777e5565c914833fed2b2e48a415ff6d59724520dbfa60d3922906dfd5069c914836fec034e48a41b7f4c9a724520dbfb04d3922906dfe3369c914836fea1b4e48a41b7f54da724520dbf906d3922906dfd8369c914836fec9b4e48a41b7f551a724520dbfb08d3922906dfd8569c914836fecab4e48a41bfe4c1a724520dfda84d3922906fde3369c914833fec9b4e48a41bef911a724520cffb28d3 else 0x8524d20dfda42c29269067fd91614934837ef19b0a49a41bdf54d8524d209ffb66c2926904ffcb9614934833fedcb0a49a413ffaed8524d20cffa62ca9269067fd81654934833fed8b2a49a419ff60d9524d20cffb66ca9269067fdb8654934833ff5db2a49a41bfe4419524d20dff260ca926906ff611654934837f690b2a49a41bdf5459524d20cffb22ca926904ffdb1654934837ef19b2a49a419ff64d9524d209ffb66ca926904ffcb8654934827ff5db2a49a41aff5468824d20d7fb2344126906bfd53a20934835fecad1049a419ff54d9824d20cffb6acc1269067febb660934837fb08b3049a41bfb4859824d20d7fb02cc1269067fd91660934827fed8b3049a41bfb5499824d20defcaacc1269067fd95660934827fedab3049a413ffaed9824d20cffaa34c9269067fd81a64934833fea9d3249a419ff6169924d20dfdaa54c926906f7e55a64934833fecad3249a41affa229924d20cffb314c926904ffcb8a6493483ff2d9a4248a41ff96d12124520ffcb6a90922907fe5b848491483bfadcb0248a417fdaed8124520efeb6ac89229077f5b764491483bfadc32248a41ff96062224520ffe22099122907fe5214c891483bfac8a6448a41bfb6893224520ffd2e0a1122907fe58150891483ff5002a448a41ff94415224520ffd260a9122907fe970548914837f6d02a448a41ffa2c15224520ffcb02a9122907fe591548914837f6d3aa448a41f7b2dd5224520efd972a9122906fedba54891482ff75daa448a41ffc4415224520ffca42a91229077f591548914837f6d12a448a41b7f69d5224520affb72a9122907ff11060891483ff290b0448a41efd6058224520efeb22c1122905ff5b1608914837f6d130448a415ff6e58224520ffca42299229077f59114c914837f6d10a648a417fb6c85324520dbfb4e299229057fdb914c914827fedd0a648a41ff94855324520efeb22a9922907f6d5254c914837f6d12a648a415ff2e55324520ffe220aa122906ff9a055091483ff290aa848a41dfd6455424520ff5a84aa122905fedb2550914837ded22a848a41ff94857424520efeb22ba122907fad425d0914836fed3ae848a413ff6e97424520fef4012a922907f751095491483fbc984aa48a41fde5c25524520defb412a922907f752195491483fbac0caa48a41fdd6465524520fedc452a922907f6d42954914837bed14aa48a41fdb2ca5524520febc672a922906f7da795491483bbe5ccaa48a41ffc4425524520dff3412a922907fe52195491483bfac8caa48a41fdb54a5524520dfdb452a922905fecb2954914836fed3caa48a415ff2e65524520ffe220ba922907df9705d491483ff290aea48a41dfd6457524520fedaa4ba922906feda25d4914836fed3aea48a41ffc4408524520dff34042922905ff9b021491483)) else (if i<9 then 0x77fd5165493483bfec0b2a49a41dff5959524d20effb0aca9269077fcb865493482ffe5c32a49a41bff541a524d20dffac0d2926906ffd80694934837fed834a49a41bff545a524d20dffac2d2926906ffd71694934837fec0b4a49a41bff6c5a524d20dffaa4d2926906ffd62694934837fec134a49a41bff6c9a524d20dffacad2926906ffd85694934837fedb34a49a41bff6dda524d20dff970d2926906ffdb8694934837fedcb4a49a41bffaeda524d20fff220bb126907fed215d893483bfec8aec49a41bff6857624d20ffdaa4bb126907efd655d893483bfecaaec49a41bff6957624d20bffb6abb126907ff91061893483ffcb830c49a41bff6818624d20bffb60c3126907fed2161893483bfec8b0c49a41bff6858624d20ffdaa4c3126906ffda261893483f7eb2b0c49a41dff2558624d20effb2ac3126906ffda561893482ffedab0c49a41dff5419624d20effb00cb1269077fe5565893483bfebab2c49a41dff6159624d20fdfacacb126906ffda5658934837fea834c49a41bff601a624d20dffcaad3126906ffd75698934837fec2b4c49a41ffe4418724d20ffda42c3926907dfd7161c93483bfec8b0e49a41bff6858724d20ffdaa4c3926907dfd7561c93483dfec2b0e49a41dff6558724d20dffb4ac3926905ffdb561c93483efebb30e49a41dff6598724d20dffb4cc3926905ffdb661c93483bfecc30e49a417ffaed8724d20effacacb9269077fd8565c93483bfec332e49a41bff619a724d20fff22144126907ff970a20934837fed051049a41ffb4868824d20eff923441269077fd91a20934837fed0d1049a41ffb54a8824d20effb2b44126906ffda5a2093482ffe5ad1049a41dff65e8824d20dffb4f441269077fd5066093483bfeb033049a41dff5459824d20effacacc1269077fd7566093483bfebb33049a41bff6959824d20bff96acc126906ffd506a0934837feb035049a41bff601a824d20dffb60d4126906ffd516a0934837feb0b5049a41bff5c5a824d20dffb02d4126906ffdb16a0934837fea935049a41bff589a824d20dffcaad4126906ffd656a0934837febab5049a41bff615a824d20dffb2ad4126906ffdb56a0934837febb35049a41bff659a824d20dffb6cd4126906ffd876a0934837fedbb5049a41bff6e5a824d20effcab4c9269077fd65a6493483bfe42d3249a41dff6169924d20effb0d4c9269077fe88a64934837f6d9a4249a41bfb6d52124d20dfdb70909269067fc98544934827fe5c2a249a419ff2e58124d20cffb72c0926904ffebb604934833fedab2249a419ff6e19124d20dfda62a9126906fed81548934837f6c8aa449a41bfb6c55224d20dfdb66a9126906fedb8548934827fe5caa649a41bdf6065524d20defb232a926906ff910614934837fc9830a49a41bfd845 else (if i<10 then 0x3aa64c241bff6e95326120bffd76a9930907ff91055098483ffc982a84c241ffe5c15426120ffda42aa1309077fd91550984837fed0aa84c241fdf54d5426120dffb4eaa130905ffebb55098483ff690ae84c241dff6457426120dffb42ba130907fed525d098483fdeaa2e84c241ffe4425526120fff2612a930907fed2195498483bfe48caa4c241dff6465526120dffb432a930907fed42954984837fed14aa4c2417ff2ce5526120fff220ba930907ff9305d498483ff690aea4c241dff6457526120dffb42ba930907fed425d498482ffed9aea4c2417ff6d17526120effa60ca9309077fd3165498483bfea0b2a4c241dff5c59526120effa64ca9309077fe3365498483bfea1b2a4c241dff5cd9526120eff966ca9309077fd7465498483ffc9832a4c241ffb5499526120effb26ca930905ffdb365498482fff5db2a4c241bff4c1a526120dffaa0d2930906ffdb0694984837fe98b4a4c241bff505a526120dffaa2d2930906ffd71694984837fed8b4a4c241bff4c9a526120dffaa4d2930906ffdb2694984837ff19b4a4c241bff50da526120dffaa6d2930906ffd73694984837fec9b4a4c241bff6cda526120dffaa8d2930906ffd74694984837feda34a4c241bff6dda526120dffb72d29309077fe3365c98483bfea1b2e4c241dff54d9726120effaa8cb930906ffe3369c984837fea1b4e4c241dff54e9926120effcab4c930905ffcb854093482fff5daa049a41ffe5418024d20fff2c0c0126905ffcb560093483bfedcb0049a417ffaed8024d20bff970a8926905ffcb560493483bfecc30249a41ffb5415224d20ffdac0a9126907fed8054893483ff6a8aa449a41ffb6055224d20ffd970a9126905ffcb854893483ffc884aa49a41ffb4865524d20eff9232a9269077fd91954934837fed0caa49a41bff68a5524d20eff9312a9269077fd9895493482ffe5c4aa49a41ffe4416524d20fdfac0b2926907ff97059493482ffed82ca49a41ffb4856524d20effb22b2926906ffda159493483ff6a92ca49a41fbf5896524d20dffb44b2926906ffda759493483bfe5caca49a41dff6e56524d20dffb74b2926905ffebb59493483ffc882ea49a41ffb4857524d20effb22ba926906ffda15d493483ffc8810a49a417ff6c08524d20ffda42429269077fc9121493483bfec890a49a41bff6848524d20bffb6242926905ffdb921493483ffc8830a49a41ffe5c18524d20f7fb00c2926906ffda061493482ffed830a49a41ffb4858524d20eff922c29269077fd91614934837fed0b0a49a417ff6c58524d20ffdaa4c2926906ffda261493482ffed930a49a41fdf5958524d20dffb4ec29269077fd9861493483bfedcb0a49a417ff6e58524d20dffb74c2926905ffebb61493483bfea832a49a41dff5819524d20effb00ca9269 else 0x520bff970a9122907ff58160891482ffe5ab0448a41ffd6045324520bffb7029922907ff52154c91483ffac0aa648a41ffb5095324520ffdaa4a9922906ffda254c914837fed3aa648a417ff2e15324520eff972a99229077fdb954c914837fedd2a648a417ffaed5324520ffeb02aa122907f7d53550914837fed3aa848a41ffd6057424520ffdaa4ba122907fbd545d091483ffa90caa48a41ffd6065524520dffb452a922905ffcb395491482ffe5c4aa48a41ffd6057524520ffda84ba922905ffdb35d491482ffeda2ea48a41ffd4848524520dffb4442922905ffdb221491482ffed990a48a41ffe4c18524520fff2e0c2922906ffda061491483ffa90b0a48a41ffd6058524520ffda84c2922907fed52614914837fed130a48a417ff6c98524520fefaa6c2922905ffcb361491482ffed9b0a48a41bff69d8524520eff972c29229077fdb9614914837fedd30a48a417ffaed8524520effaa6ca9229077fd7365491483bfec1b2a48a41dff5d19524520effaeaca9229077fd8565491483bfe5c32a48a41ffd6059524520bff970ca922906ffd32694914837fea934a48a41bff609a524520dffb64d2922906ffe33694914837fea1b4a48a41bff54da524520dffae6d2922906ffc83694914837fec1b4a48a41bff6cda524520dffae8d2922906ffd85694914837fedc34a48a41ffe4c18724520ffeb02c3922907fed4261c91483ff6a930e48a41f7f5cd8724520effb26c3922906ffda361c91482ffed9b0e48a417ff6d18724520fbfaeac3922907bfd8561c91483bfecab0e48a41bff6958724520bffb6ac3922905ffebb61c91483bfea9b2e48a41dff60d9724520effb08cb9229077fd8565c914837fea1b4e48a41bff60da724520dffb08d3922907ff521a2091483ff6a151048a41ffb54a8824520dffb45441229077fd95a20914837fed2d1048a417ff2d68824520effb2f44122906ffda7a2091483bfea9b3048a41dff5d19824520effb0acc1229077fd8766091483bff4433048a41ffd6059824520dffa64d4122906ffd526a0914837fec135048a41bff6c9a824520dff8a6d4122906ffd536a0914837feaa35048a41bff5d1a824520dffcaad4122906ffd756a0914837fec2b5048a41bff655a824520dffb6ad4122906ffd876a0914837fedbb5048a41bff6e5a824520effaa74c9229077fd85a6491483bff4453248a417ff2cd5126120bff966b8930907fed3154898483ff6a0aa44c241ffb5c55226120ffd966a9130907ff93054898483ff6992a44c241dff6e55226120bffd76a9130907fed2114c98483bfec88a64c241bff6845326120bffb6229930907fed2154c98483bfe48aa64c241dff6455326120dffb42a9930905ffdb154c98483ff6a12a64c241fdf5495326120dffb44a9930905ffdb254c984837fed)))) else (if i<16 then (if i<13 then (if i<12 then 0x14390435f432e42fd42cc429b426a425a423441f841b141804165413f410e40e840ac409c40764045401440043fd33fa23f663f563f1a3ee93eb83e873e773e463e363e263e0b3dfb3deb3dd03dc03db03da03d853d753d653d603d5b3d093cf93ce93cad3c873c613c253c153be43bbe3ba33b723b4c3b1b3aea3ab93a7d3a4c3a0539c939a33946390a38d9388738613830381537ef37c937ae377237623752374237323722371d370d36fd36ed36dd36cd36bd36ad369d369836933683367336633653364336283618360835ed35dd35d835c835c335873540353035203510350034f034bf348e3468345834483417340733f733b033a0336f335f332332f232e232a632753265323432243214320f31e931c331b33182313030ff30ef30be3082305130202fe42fd42fa32f7d2f572f472f162f062eb42ea42e5d2e4d2e062dca2dba2d7e2d6e2d5e2d2d2d1d2ce12cd12cc12c852c752c5a2c1e2c0e2bd22bc22b9c2b342aed2aa62a5f2a3929e729c1296f2949292328e728c12885283327f727b02769271726c52668262125fb25b4258e2547250024cf2488243623d923922361232522de2297227c2261223b221521fa21ea21da21bf21af219421792169214e213e212e211e210320f320c220b220a2207c2056200f1fde1f971f711f351ee31eb21e6b1e5b1e141de31db21d601d2f1ce81ca11c7b1c3f1bf81bc71b8b1b7b1b601b451b2a1b1a1aff1ae41ac91ab91a881a571a261a1619f0199e196d193c18f518b9187d1841181b17ea17c41788177817521721170616f616e616b516841648163815fc15e115d1157f152d14e614c01484143d140c13d013b5138413741343133312e112b012a01259121211cb1184113211221112110210f210e210d210b7109c106b105b104010300ff40fe40fd40fb90fa90f8e0f7e0f6e0f5e0f4e0f1d0f0d0edc0eab0e7a0e490e390e1e0ded0dbc0d8b0d5a0d4a0d190cf30ce30cb20c970c7c0c610c300c0a0bef0bdf0bcf0bbf0baf0b9f0b8f0b690b170ae60aaa0a9a0a7f0a6f0a5f0a4f0a290a0309c70980095a091e090e08d208ac085a082907ed079b078b074f0713070306e806cd06b20697065b064b062505e905c305870556051a04e904b804870440041a03de038c032f031f02f902de02ce02be028d0251024101ef01920182017201620131012100e500a9006200310000dffd10a8926906ffe88644934837fec0aa649a41bff6e15324d20dff972a9926906ffdb954c934837fe98b0a49a41bff6458524d20dffb62c2926906ffdb3614934837fedcb0a49a41bff6059524d20dffb06ca926906ffe88654934837fe5c32a49a41bff54d9824d20dffaa74c926906ffd85a64934837ff4453249a41ffd60d2124520ffeb0299122907fed7350891483ff65c2a448a41ffd6055224 else 0x37dfd7dcc7d9b7d757d397d137ccc7ca67c757c2e7be77bb67b907b6a7b4f7b1e7b037add7ac27abd7aad7a9d7a8d7a7d7a787a687a587a487a387a1d7a0279d179c179bc79ac7970793478f878e878b7787b78607850782a781a780a77d977c977a377937762773c772c76f076ca76a47689766e765e7638761275ec75c675a0757a754974f774d174ab7485745f742e740873c1737a7349733972fd72cc72a672807270724a720371c771b771707160711970e870d8709c70767050701f6fee6fde6fce6f9d6f8d6f7d6f2b6f1b6ef56ec46eb46e786e686e586e3d6e016df16dc06da56d746d646d336d026cd16cc16cb16ca16c7b6c4a6c196c096bd86bc86bb86ba86b986b5c6b4c6b3c6b2c6b1c6af66ad06aaa6a846a746a4e6a1d6a0d69e769d769d269c269b269a26987697769726962695269426932692d691d690268f268e268dd68cd68bd68ad689d688d686768416831682167f067ca67ba67aa67796732670c66fc66ec66dc66cc66bc668b667b666b6645661f660f65e965ad65716556651a650a64d9649d648d6467642b641b63be6398635c634c6310630062ae629e624c623c622c621c61e0619961896179617461646154614461346124611f610f60ff60fa60f560e560d560c56094606e6048602260125fec5fa55f745f645f285f185edc5eab5e855e6a5e5a5e295e035ddd5dcd5d865d765d3a5d355d305d205d1b5d0b5d065d015cfc5cf75cf25ced5ce85ce35cde5cd95cc95cc45cb45ca45c945c845c3d5c2d5c125c025bf25bd75bc75bac5b9c5b815b715b615b515b415b1b5af55af05ae05adb5acb5ac65a955a645a335a235a1e5a0e59fe59cd599c596b593a58fe58c258b258a258715861583b582b581b580b57e557bf578e575d574d570656bf56af569f568f567f566f565f5623561e560e55fe55ee55bd55b855b355a3559e55995594558f557f556f556a555a55555545552a551a550a54fa54ea54da54ca54ba54aa549a547f546f546a545a544a543a542a541a540a53fa53ea53e553d553c553b553a5539553855375537053605350534b533b53365326532152fb52bf52ba52aa52a552955259522851ec51e751ab519b515f514f511350d7509b509650865081507150615046501550054ff54fc44f934f784f684f584f484f384f284ef74ee74eab4e904e804e704e604e2f4e1f4de34da74d974d664d1f4cee4cc84c814c714c354c1a4bde4bce4b9d4b8d4b7d4b6d4b5d4b2c4b1c4ae04ac54ab54aa54a8a4a7a4a6a4a5a4a4a4a3a4a1f4a0f49ff49ef49ea49da49bf49af499f499a4995498549804970496b495b492a490f48ff48ef48c948984872484c48314816480647ca47ba47aa476e4711470146d046b5469a468a467a4649461845dc45a0457a4549450d44dc44b64485445f442e43fd43c) else (if i<14 then 0x4bf29bf03bee8becdbea7be8cbe7cbe61be46be20bdfabdd4bdc4bdb4bda4bd94bd6ebd48bd22bd07bcecbcc6bc95bc7abc5fbc4fbc3fbc2fbc14bc04bbe9bbcebbb3bb8dbb5cbb41bb26bb16baf0bad5bababaaaba9aba8aba64ba49ba39ba1eba0eb9f3b9e3b9d3b9c3b9a8b998b988b978b968b958b948b938b91db902b8f2b8ccb8b1b88bb865b83fb819b7feb7eeb7d3b7a2b77cb761b746b720b6efb6d4b6b9b69eb66db647b62cb606b5e0b5d0b59fb579b55eb543b51db50db4f2b4d7b4b1b496b47bb460b445b42ab40fb3f4b3e4b3beb3a3b388b362b352b342b332b322b307b2ecb2dcb2b6b285b254b22eb213b1f8b1d2b1acb186b16bb150b135b11ab0ffb0e4b0beb08db072b057b03cb021affbafe0afc5af9faf79af5eaf4eaf3eaf23af08aee2aebcae96ae70ae60ae45ae09adeeadd3adadad92ad6cad5cad36ad05aceaacc4ac9eac83ac73ac4dac32ac22ac12abf7abdcabccabb1ab8bab65ab4aab3aab14aaeeaad3aac3aaa8aa82aa67aa57aa31aa16aa06a9e0a9c5a9b5a99aa969a943a928a902a8dca8c1a89ba875a865a855a845a814a7eea7c8a797a766a71fa6f9a6c8a697a666a656a646a636a5e4a59da58da546a4e9a4d9a492a440a430a3f4a3ada37ca31fa2f9a2a7a276a245a214a1e3a1b2a1a2a171a14ba10fa0e9a0d9a09da06ca05ca036a026a016a0069ff69fba9f949f6e9f5e9f389f079ecb9e8f9e5e9e4e9e1d9dec9dc69d959d4e9cf19c949c6e9c539c229c079be19bd19bb69b9b9b6a9b399b089af89af39aee9ade9ace9ac99aa39a9e9a8e9a529a379a279a0c99e699b599a5998a99649954994498fd98c198b198a19891985598459835982597e997e497be97989793976d975d972196fb96f696e696b596a5967f964e9612960d95dc95cc95bc95b795a795769571952a94ee94de94b894b3946c945c944c943c9421941193f693e693cb93bb93b693a693969386936b93669356934693369326930092fb92eb92db92cb92bb92ab92a69280925a925592249214920491ff91ef91c991a3919e916d915d9137911190e090ba90aa9084905e902d902890188fe78fe28fd28fc28fa78f8c8f5b8f4b8f258ee98ed98eb38ea38e938e838e5d8e4d8e3d8e0c8dfc8dd68dbb8dab8d7a8d5f8d4f8d298cf88cd28cac8c868c608c2f8c098be38bbd8b768b508b148ab78a918a6b8a458a1f89d889a78997897c894b892588ff88ce888788778851882087fa87d487a387938762870586d486c4865c86368626860085da85b48562853185218511850184db84aa8484845e8438840783b5838f83698343831d82f782b0827f826f825f824482298219820981f981de81c381b381a381938162815d814d810680bf80788068804280277feb7fdb7f9f7f797f537f387f127f027ed17eab7e857e547e2 else (if i<15 then 0x42501e07c03080842128dc6a001840946e35000c204a371a800610251b8d400308818228006081580c9401789f17db4a001840946e25000c204a37128006104105115480180788888042a018060c12094c6806125004a14a001821400305089a401e018484504a500d112a012060aa0090008590a0609c508a001008c61481f80c0952803d028384a0dc0d40613db06e0940d406145485112a012060aa00a060ea007c030612a5000c183df8a3de5000c2bc57aa134064a00946173280060c1efc517328006141c841efc517328006140f05001830a4031ea83f940128141dd4f00e9128080f43704a06a030a148063d507f28025028386209f407c12a5000c2db6e01d207bca02837084a54025401284a8025095004a15d509a0fd5004a2849084a940030612bdb459940030b1265000c184af6c1265000c284a7712800610257b689328006142c80c94012880485005901840180fe500592065f6c0302cca00946f6d2802c8fdb00c07f2802c95fa450771c01db4599407094031fa3b68b32801e828406208599401286889500903055007807481eea808943805f44b2a80a81821480603f0de12950028383f019ed83204a5409641420310431046f842528e01807888182ed81e84a540030a967db04a540030bed94700c0940fc0f180f0b809410481645c01e0bc4dc02dbf2dbd7dbb1dbacdb7bdb76db5bdb35db1adaffdacedab3daa3da93da78da3cda0bd9fbd9e0d9c5d9b5d99ad97fd96fd954d944d929d90ed8f3d8e3d8bdd897d887d877d867d857d847d82cd81cd7f6d7dbd7cbd7b0d78ad764d73ed718d708d6f8d6e8d6c2d691d66bd645d62ad61ad60ad5fad5ead5c4d5b4d5a4d594d579d569d559d549d544d534d524d514d504d4f4d4e4d4d4d4b9d4a9d499d468d458d43dd422d407d3f7d3d1d3b6d39bd375d34fd329d2f8d2d2d2acd2a7d281d266d240d225d20ad1efd1c9d1aed188d16dd147d12cd106d0ebd0d0d0b5d084d069d059d028d002cfd1cfb6cf7acf49cf23cf08cee2cec7ceb7ce9cce76ce66ce35ce04cde9cdb8cda8cd8dcd7dcd6dcd47cd2ccd06ccebccc5ccc0cca5cc8acc6fcc54cc39cc1ecc0ecbe8cbcdcbbdcb97cb71cb56cb46cb36cb1bcb00cadacab4ca8eca68ca58ca32ca17ca07c9e1c9d1c9c1c9b1c9a1c991c981c95bc935c925c8ffc8efc8c9c8a3c87dc857c831c816c7fbc7d5c7afc79fc784c774c759c733c718c6f2c6d7c6b1c696c686c66bc645c62ac61ac60ac5fac5eac5dac5bfc599c589c563c53dc50cc4f1c4d6c4b0c48ac46fc454c439c41ec403c3e8c3d8c3b2c397c387c361c346c32bc310c2eac2cfc29ec283c268c24dc232c217c1fcc1cbc1b0c18ac16fc154c139c11ec10ec0fec0e3c0c8c0adc092c077c051c036c01bc00bbfe5bfcabfafbf9fbf8fbf74bf64bf54bf4 else 0x8e0fc5f6c3ba50103707db3a90193882503f940715211dded9eac0c0f5280c7d03f141e852019280fa1be29f48952807b942505ea84d07f28025142484ef840607d1c41cc837c23bbe2fb68183a0a0203a383ed9d484a540030a6a42edb4708253b603c0fc1e974707db3df094a80061431074c00c0bc30180af47606d300b45c4d503e9d53a6362eb6d40030c0ac06698571354141b5b222088a826a82832b8c35354603016ab8c351201e8283eb6c3416061601648ed6c9230d0283e98c90ae07adb242a01e8e952ae30d6482cd5c34ae07a3b032b8c35354bb7f4160651dada6ae1a3e8ec0d8695c4d5282dc340a3242b803e6d1d81b0d2b89aa0a0db7f414a9c01ad9506483e8251d81b5b61a9aa0a0f0cb47682c0dadb0d4d50508d53a3a6fe48571868db170d2b81ea9d1ca0b2461a9e869e98696a8f476825533d30d648368ed04aa70d4f4c906c353d0142d5268ed0581a7a61a5aa6d1da0b0361a9e8b54141f54e8ed040bb2461a9e80a11aa7476b6d8ba60061b5b698d8a03080235b2a9c34920ba3b412a9d6d86b241b54e8ed04bd32461a300c0bc297003041780f00c181e0bc03061040f0803041184062b81006080c5702408ae04818292d5c095c050004548400ab81206080c0680995c110004e2842504101830940e80f0dc701609409e5c03430520940d02f122571a1701787b81f301e0bc0307f141a01603c104a1481682c01015e5c0283fc5e340565c13cc00be9009e5c034307608270952e01681e018605bd238d4b827c50382e006102902d0580d0254b805070112e01f8322798059d201a4b80506895c6ba40f617007cc0782f00c1fc50680580f04128527aa0d0254b80506753d238d4b82798068128144b828750ab8094209417841282f0900055c04a12b80942094178480020d01404a0bc40680a02505e20340501282f10248425041018371c0580444904f2e01a1d0985903c17892e00f05901840940d00b04903c104c0b80f028970164b12dc771a8b32e0be60058279700d0b1265c01e182e02d2e00f13cc4b80b23e34014144b80b250ec10b32e0250c2a059094178892d5c095c050006eff48e34ae0977fa471a5704bbe92f8d25957051be1f8a0d01401f5705e00ae04800214be283403c15c142b83852f8a0d00f057050ae0fe6124834094ae014180f05e0183f8a0d00b01e08250a4f541a04a9700a0cea7a471a9704f300d025028970597012840d01404a0bc40ec11edd238d4b820760852f8a0d00f0579700a0eae00f00c0944400105c0595c04a03c030c0b80b2b80940780618170165701280f00c302e02cae02501e018605c0595c01e094904061c80043b043b048004e28435067a00c10f401829e8d200f00c24f40cf409429e8103c12839af4018504410921018a8048182a80060803050304830480))) else (if i<19 then (if i<17 then 0x13aa10b216900fc1303020620c080021481f8282801094240c109410101f8beda5000c2008084d088f1650159285807723825034280c0fc5f6d28006101600c09a0f64701f304a7712800613db4a001830180b01e84d91c07cc02020303d48e3aa1c8a0202909a403f0640782914d487e28ee0f528081242188237c20c421e8061d50e441521f6d0303d5d59405b6cc0046e02a3836d9a4090306db04dc06db04dc06db306128e0db60a00082db07475b615b60a8e08001242040c1000c08520180a01e90060011206080c080c0a80f46134dc02807a43700f4140c2903d050307a15040318308060415ba9b6da80291500074704db82b8180f7501415ba9019f16db01607aa8106a42006db05205040a80f440040609030406041e84a94003080f42502201840952380f0f507a50181341ec8e03e50180f4290c26c8e1ee07c8134060b707e07cad201f81e0a440ca078290c1e8f503c1489032503d5184d940f54251032bd51ee3a083b9eac4a1ef280a1281f81e0a44940f541e83f23d58952807b91eaca00943dc87d07403d07e4f8b12a500f725b607a3d41f92db041f8b907a30952380f0f507a509a1101e84a940774d2381e03d06841736d852385c83d18b73701341f90060f707e309a0305b83f03e5b6c10872801f8c5b83d0940fc80f47a81e0a44b6c17ab12a500f7206e0940d41e93e283bb6d2801f945485ea82c8952807b94eeca00943dc9f16501f41ee416e0301e85220490db607a3d41f92a406a404251481548084a084a2902a901a9013aa176d52055202ed82005d509b525065c5540128e124352020f40f80c2b2148a03026828183f2b207c61281fea02b2148a56420fd5004a2b2407e564140ea43b613b65401281f91db1590503f6c1665000c23b60952801e93db04a04403080301ec8e0b207ca1340603f03e48b20302683d91c07cc165db03d03c148a1940f052183f770ed81ebf48192802ca0773f48192802c942503f03c1489141dc03f07b166503f4380c07a14860302945909a4893520412824852180c8b21507126a409db4a0a911642915800506054705a405030408302e08283028302c182a383a38280020006e0e8e0a8e0bb60e8e08f576c269016901492d20477c2040c100eef8a9287b8e828654a0832fa2591d0601016001600140c1018109a0301e873205207e03014103783d0a8360c100e10560fc3985222000e8e0fb60560300987c0e6635210020fc3e02823b60fc5540ed87a83f280176c1483991a407db2a078a96429143203f2b20a09a3820041f87c0504010140c1003f03c14860fc0f05218080fc5f6d2800611eafb6018134254a00a0707723825034200c0fc5f6d28006100604d07b2380f94253b89400309f17db4a001840180f426c8e03e501017521281fca0230601014861940f0521c else (if i<18 then 0xc1292080c3876084d03e0f47b7c0f84a07a409210181b426cf403e509214001de807c5bd02681f290078a03020f42692303e401807c40f40612309a4600106002f7a00c202b0260237a137a04d09456480182c00203020f43904d1830016bd006101e80c0e413481643bd02507206040d414001dbe1400104fbd0065480e45a0c1010109410c21de8754138f7a1d504e35e8754138c336f40e430101de8078918f7a51a2461c8808c3bd025123182308106076f85e2856fb00120608106053b05060506040e602b7d830900058304016426a426a4241820203bd0251591ef4b8a1c86124212821377a1590944094005800d030406041e80c0e41349f141879800abd006182687a03e3690169014001dbe10c418181ec3d06921d508590ef40e40c0601f7a0721808085b9e803060203305704f3d0a1341a4f478a564ac000408138589e81281a140607e2f989e803080b00604d9e807ca1d8216e7a00c180c0581367a01f28080872f8ae800639803f3d00f20ea8ea0e436900ca7a01e0a459be1f8a0b0770699e850c41f3003031dd50ae09e7a1c4704775d5058e8028c0c9e870461352109210193d0ea8ea0e451ddf17cc4f48183a8d5203520200941418109417301094105c5084a080171427542030207c0615907a45e8030268f7a15903e3de8564250ee2877a1590943baa144268285e8128d0337a1590d2473018197177a1230e25b8a109a0d17a04a2b25819bd2a407224f48b213471643d8ae2867a04a09213480322c84d184d0b212877143e60064f4b8b1643d9ae28426cf409407a2c94009e810348080000000000000202009419be10101dbe104e1280f3d55e8030c1a83280060a500650065034814a00801010240c10020204818202028182d20252350052184d03e0f46040c102060801ee8e2b207c80f40615903e42900302a03d20490810304db06251b8d400f48128dc6a001840946e00607324a001813429100604d07b2380f940604d07b2380f94248580041fea00181488c003a80ac85218060959080c083d03e1486ee00f052183f54003029101e81f018148816425201f830d4012829183704a07ec68ac85232000e8e0d4808080a00085909a9a900fd8d0522800404040500041fd060f80a08003000800004a00b48080040412802eda500a500650065006500404064705800506054704acb4812060810605c1050605060583054705000583040164298826a42a38281826a42418200b21010102060800404012b5015919d5291a8025052280248408182004329f43aa3a0a0f4711d503e40560fcd48e80a45002b0ca7d0ea8e82823082b0ca7d0ea8e82859082b0ca7d0ea8e8280107e6a474052282b0ca7d0ea8e828103040020212821280089e2ea02b21488818203020f40602809a407e14806028203d0a82690169014 else 0x6081d4bc1487f140281f016ae0ad2020d1208521a000e82098e0eb8068148675421642d235c03005040ec10a4110140c0084a1206084a5700782910250011200082703c0d0609c1d04a068405a1281a0c0a81e0a43078078290c2f01e0a43970e381385224b803c0a072e0250521bf404e1486f7fe2ba00a507a5c180f02706830a52e1c7027068505bf14173a005805a0f4b843d30bc07872e00f0341cb809415c615dfa0341fc505a15e0f07297060da0b62f03420080b00010202c15e5c034202d0940d06178ac834185805a1281a13cc7c505c0b40f8b83008081e0820d07208d486d06840bc078290c1686d06830641780f05224820cb83aa09c1a1016fc505ce801601683d2e1002c2bcb8068411c1b53f141702c7400580a41e97099700781a0c11861e1d506839701282b8ceabf40683f8a0b7cc06d0af07a5c1c254b803c148812421d8237c27543d034186d05b1781a100a81e0a430bc078290c1e01e0a43970f541383423a9f8a0b9d001683d2e0f2e00f0341bd30bc07870f1ea8341cb809415c6f547a8341bdff30f542bc1e97060952e00f05225480ab80948634209452055203520212835218d08ead48154809d5084a0dd50a81282f100800375429047f3017825182b85208fe602f04a35d50a411fcc04a0bc60921a900fc1a0d5c04d104ad700a0ac8522d48084ad700a0ac8522ab80940a07ae0ac8281d4863422465641f8cac84acab80940d09ae0ac828182703c0d061641684a068404e0e825034201503c14861641e01e0a44970e381385224b803c0a06e8204034970164afd0138521c4b74112814459970603c09c1a0e5c05903c0d0912991ba08b21040f19eff988100d25c059304a9700782910294490ae33a6164290e24d4817988bd164291224d48101e8b21486c1941080c182c683a08280020d041504169016901492d2043dcef8bcc7c54183d887d0204001505f143921e1ec5f30a0be2a1e1ec549692b8d2591ec5010103aa091e052279800a02d5c0f62ab8002260c1d700d0290d00074104058575700d086a42148220281b480f984bc96429135c15905033be1811a08290440505088078290c1744a07e35040044ae0008900041f84a068307e1281a0c2201e0a4302a078290c2f01e0a43078078290e5c3d504e0d08ea7e282e74005a0f4b83cb803c0d06f4c2f01e1c3c7aa0d072e025057184a9700782911ea8f606831ede61ea85783d2e0cf5429047f30178251bcc7c583c3d880203f141a01603c104a0b8250289704078078290c1e01e0a4390417aa7d01a0c7b7987aa15e0f4b8379805c128144b828a90f987aa1b42bc1e970609417aa14823f980bc128c0b8144b809440921f3077fe2c1e1ec507e1281a0c3e0f60e63f31f160f0f6244a5710781e9341074105d4ab80940d086a43a0820b80b2b803)) else (if i<20 then 0x4a48625159144a2b228955201f8e25449a9038cb77d060eefe8e690340c1bbe83047de32a08bbee08b77d060aefa0c10eebbfa387a3aef88775df0da3352169177d250eefa4a492d2081bc00880400176c305c0340b0c2186f107c0bdd6900fc60200988d48404041e9f411df01021c4101803440fddc00d180d0a403067d0060806043284a026307a04cfa0c773a911f40bd509421dd238ef8c2501310ee09f47ba1286030fa08fa04efbc5094378a1284020302015881fbb681010c8ea60402b1e8e810207fa3a040defe8e810302a1484178060541eb6c34148697c237c21d83b175b0f60e64d8a3d80f8f5b00c04c3057ad80602624a9d6d8682910062df02d8695c4d532820181487b143d61a0a44d8a1eb0d05226b6d8b868291004055c0541074702b4192a74c64857074452a4174f4c90a80d80020bb4720c9ab8695c1815a0cd1d37e54e4857186918003a08166009e992150180a682c0d8027a4d554070101d05b143e8ea0e65d6da3b5c648c343a8d8035b4d5050401a017472df95386b242b842b8d8a0a0604f4128e952bd30d6483eb6541b14141362eb6d301489b175b0330a4402db155c03426b6d8aa381a126a8762e985701488034060341ec5d30ae0060522ec507a0a0735432a75b6c55400d0ba636283f06841be19aa0fc1a0f0005410700056a87416b6c0192039975b2d50503d8a10c140c06041a2b80a435040b80603f26c5056ae0060282ec5026ae01e8342e989e8aa429126f875b6985aa1489b175b0330a44d8a0fc1a0d5480c05c0f4803354ec55e9a801e9809c08d04aa5476b6c9186900ae0468ed04aa57a648c34840c020290f0360016b655212814130360010430940a0637c2054290820852101d0bc03029100e80c078148807c26cb807a41ec10025c055c0400540f05218100075c1482340d029160f04113000a826002d7015c140f5c0342b214880182565800a0402e570301010b210945235c028060148c12b5c31a2b2148a8003a08352025200eab8018148b5202800216426a580548482148a0570078290e8344a07e3003c07a14868002c00efd480880a0aae01385218100075c1a005a1488164211013852198e57009c291009fc54180d15c1400bb5c0280a44400101010206081d5700781a101ae09181e2340d0129b5c034247468291411855c01e0a830052291ae09184a04a6092104616001504c005a082f14ac8903058328212b808183058d050004d4b061002c84d485410503041a23c0ae301a90a000906085908080835c14906830941782b8c05235c0570a4440010921020609d53e80d060d15c057180ef84d07a0d0880020d0fa05219d53e80d0648cea9f406843aa7d01a0c2c84ea9f406833e80d0290ceaa823e80d08040c1f8a8301a2b82010004040425300104a00220a4978ac834220 else (if i<21 then 0x24807a254491ddf4182bbec690e0eefe8212000ddfd04250577c368cd48525348bbfa08977d2524b492405c0584f4da431a050405c1d04d20477c27d020201380b184a01623be02c040c058f6138e04e058600680784f4c0f09d482e104a0ae290477c412802887b04efbc5094378a1284020205a04682182e811a086f7f4108c704c7040680c100d0182018034ac8c180270da30cc04ea40c1380701030d61061020ac0c13a0c120c081641809c6034283029d828302830203421a4741231866026c186800219803a4a1859082c1dc05063b8336df181f03c830609c349231a4a2b2078607c0f080fa0c101f06807861a6cc1231859093283c203c103e830407d0601e181e2b222b3714918ed4a0c10eedbf6a476a506093b06d4a0c102eb5283064c90f090004c70425042504250426a0c104d0ae128612821b62514919492468786128138010e44018134403026880684a2b2309409c038f6fb8e1072740209456440c1c708acbd3102709420da109409c0f0e2541e1030082705607866a40408158ea100c01a201a0d0060c1600c105701a128ac901600c1027010205812840b0250813b8e13a003c21dd37c7502c204a2b2204e0ac0f0c7702c102c03c27a656440b00f08ea842505c744a107b74022b31284566250a2515014497401ec7b7e040815c0811df0c0826400460200088009f411a908640c0800223be135210c810560204ed815808182b010205c03040341f80c18132b223be105683040b9060ad482e41030576a5060ed482e418340010dc10de13be10866e01e8cdb30005632b2f14218d0400111b808820860f5060c2203f07a6e0810cd488db306120008590843084336e216e1d1c10c414aa408a404a104da9083061342b85209448ca0ac400471081704fbc6505c305683048301708068409850604ace8e69036000ac481828200089060504382120c0a0c080d0e8e1dc24001026176c10b210c810c8102611dc0b043bb4709a404253b6002309400440c01700c180c09a0fc675421bb618ee3aba3860c34708ef841600813b60561e81e9036808056305802040b006080680c07e301a03029159200c01a20180b040b025081ebb601004c819404013184a0582353238160e470ee058305812b2d20161d520b191c1b463b816080984a148e1620b0657820f4af081e95e103f07a5787a38ac8ae295915dd2b22bba5645128a488dc20c168e690240c13e8820008cdc20c103d418207e0f4dc0c1f850004fa043706fa03f15f40f42d1c107a030008cfa00c0020f496d815e8e75247aad20290edb68e102b81820180f4098c1d83db6c307a7d07a8dd4db613d5b6c2b6c3d44832a408a404a120c292209b521060c2904d0948309a38ac88ea9491159a902094564412ae29591c4a29223ba5244ed829548184a3ba3d47128a48832 else 0x16f856f856fab8102c1dc05060d8ba600a01320015a0c10ead6c0b063b81608756c5100c09aa081d936281312df0adf082b026205781b004080265c0d80015c0822df0c0802628100fc4148202cac8a2503f11df080b3e823521b1c0fc409c0b090401312b80b9806848c60b8d4e821a00085909df0e820e82082c0282d0415700d20f0c1a12310590ab883c2a34148ac8c1a15924632b36a5040c175a95703400131c13be10af1295c0ca4034634128814a25149194943c48c656504090004058417074104ace82690340c141015701d04c6840b42800202c2031c1d0410b21d041d0410581d0413aa0584148205821482a3d32b243aa13aa0b840c3410a2503b11df080804e02c60b025080400b10300160b46e3813816183403c0a060ba4102d0584094564290dc702702c3002e05a0b06f4cac8a4102d058305a0b0414aa40a2505e11486348787a08ac882904a29230a552041282907b1c4a2922292878918cea9491159a902094564415c251d52b24894524452420b80b44a2b248955200b0ea40286351289128ac882a01e0a409e24942944a8971)))))
def oP11 : Packing:=(1724,4,7,0,0,16,0,oP11F)
def oH11F (i : Nat) : Nat:=(if i<3 then (if i<1 then 0x1e1890100ba00a00713d02810601009c00001002001a4791610b503001201100932705a01600a00002b1c306303372a17c00c00600023900910a4160327e001700001b0037320040172f800800035900710a0010100000230000610230040030cb00801200201b02100804201e1c300106007207700200407e0030a92340d24a50281780992f500600503801300400e04400e04e00004000f00231e0220255b001902b0050000030001c902401500100673f00005054643700e02f0a805e0130000010a300d06600601400503200500401300701300000101d00a0030090fe18603600005000b09d57d00d00200600f0c81ca01305000306a00000600e0060020081e403e00100005201801b00002202603e01112e00000f01407b0000f400600000a0040b204f0a800701b06602c06a01f04700700000508529300a0030050090310000ab00100401600300601605703607902b00900002905d02a00103200500503c00f00800034201f08901100d0190340af04b0150000650b105501d00403105602300307900d01503100100601400100f00406c03200301307801701500000000100006b00500000704400500f0140070000000000170000021bb01c01500001604f0090000010183290400000040010140b101800000b00000000100d01203303100001201503103102404f01202000003e00001a03801f00603904f00000000d00a0190e801602500400200c10d00800000c02a00400300f01e0270021f600400000800001902a00100500001700801b00300000a00001809200002103800400000200301000c00000400000d03a07a00000700000003b02500a2d900a00a05200300600900004000208c00101701a02400101b00600100f00001300804700101a03d04b01c04d0010000170150001c900203805b00000300000f0b01c40110451d100402600200000002904200700800000c03b00100a00200b00d03e00602501100d00600c00600001b00600400c01102b00a01d00000700700801c00006300100300200200518000401201200100802300b04100200000702a00500000700c00800800001702207c01800207d00b0000070030310180010010000010010df00300001600001501100b01600304c0000000a402800101600900004100004900000518100400000600200212b00000400302e00000700e00003d01300200104300c00000c00207100205c00006c06000101912600502a04602c0090300160010110e600000200300803702904100000000500300402301900f08400300000000100600000001a02302c03500200301700600700200000001600600100400300000906700000101e02100000000800c01302d00000600000001200000304500702505200000100400200400004501100d00b000026003000029005029 else (if i<2 then 0x2de0d060121686b0f032e209f8c077126b404d0a002028012604664071b60eef0011d83247003a60cfd408e704ef5796c20ac4024f3a002c044b010b302fa402a030aa461181409ff236790b26498dd01b1283ea30ade696fbc018800f1f05c0c99b3026da040fe057fc8e440104ea0f490571201fd427040376c06ac80499c0eea85ef60a20408908219684ade4d33eb2d0406ef062290a57615db8471704cad4c8f802918255700e0b0b6e4814c9067306b9648802199901e71a4d2047f7812ef0204a8682202a52053d91e2e81f2f0581206a082970a3b3107cb61129d06168029a08892022a00cd705c220624818b282cee00d800beee0af140afb24ab70398c07e581195842d408a6c8c0cc02a680ec300ad40f80916a5044fb41b1002a691603a4111087380e59000928120a0d4040ae65035d064860274297d20068ba08410119c06b902ee0265bb069e4104540f49065714088a0c361150e0619903de419814117280d090a2c08b1a11df90373b0748402b991fc182e6b0bae80b9082c19851e209c46116c11624841910a7ea1a05c0d9d834a60aa1a0df7835610530d4592805acd059084bfd02e5004dcc111ca38de49b10053ac1b530366e021ba0fb2c20ec066e80ce3c1a8e0299f85f5a05dc400c84155e029ae4cbd40fc10230f813d3096e608b3c25a5a61d14585a8a9c12264860107d592089e41ff2a5d41014f0151cc1be3057ec046b40a03d22f383d660c96c00e090367a2b07093fe129800f6b841c40600010ce8029a85737050da13db42439a38b5002c6099ec23cc80a07084700412c1a718243509862079241cf70661c04abe096d424d1806c7001ba0cc981e2e818dd04f0a177a801ef2652546ba803a041536208ac0c56c901f0301ba0e3701ecc0a3182e78059cf09e5c0d1340c0203f6a0b4828f53c008f24df904f949025c33cc266290c8968ddac051ba5cae05da852fb419068571307fbe0b75d22d1829bc0c62282ba032dcbeb8b09938145f429a4a4a7704b4098101328a804fd0d2160e51814f484cbf0c8008eaad25c4863954639a0931c0bf70472f0360a928fc2c80a4d7a0aade08108275f854894967002e501bab05b18465ba01c4c1608820f94bdde1a7b03452a636b69970839d40f04857f408f628e0e9e67e80aa4098e48d6600beb0509f05ab40dcac07d5826a0039780b4c5315906af407c2e826b91bd6820830d31006ef021f183690090c80c5ed152d8386401134046ec164480bae067b4990e826b2a6250468dc01240069201d200102e4100000000260000210062880240000712c62da53b04d06905c00010205201b01726b00303c07903a00d02a00000c02b06300000001f00202000000100c1ce0bd2f706f01118c0045190cf00c88d06d0340ce0fb0370080000160041200000440c81e01ae0 else 0xe3202951239fd0b5b211028190a865f4098a89a4a0030c036db0266e16d4d1cb4012750765e99bd526b185c65004ec1833d182203d910ad540cab0348f8063d02ca603d6820308033e0bec01a02c2106046cb0be6c19f9823ed8518d013c083eb81c150387209338902c827c90663406bbc0872c04ce44df801f100f10815a0822d001f22909c12686810a007a908f1d50695a394b01030910dc1e96811f60aabe012b0179284ae3052dc07d502dd5819fc4820e009642949010310107802f182cb1817880ce9e1593834ad85d4104328529f435c2807bf0b4fc073cd2fc00170709360076680d4d80bdd005cc0ed4c22b9869cb032bc013a533050360546e2c1169c0ab6a0d994c55a116742f1e24e194c4dc001fc1b20a2d3d0cd0a1ab98084286a7e0845c1aedc198d0034e46c9001948240d8048f031c097cc92f3b01e670150c0d2dc1634038e703e1a0e28d2151234e002f768a8b4022e826de011a21856d1fefbcb410be32002801a3c81506075740b375322a06836056c2934643007a2b1e0516a1257926a5a458d45ad60e25c2c62020e30983a02c681a6a8207305d7e168742184026180928c0555c1aa184e41058a4015f42ddb826b0055cc0be801c858174d0a3be0c17d152120f704659292b202c050192601ad08f48526f38604045a180b4b013df008bb0b3c2992440fd403920089ae0feb819a298ee0033c2143802a2c033b60d5240630007bb031f002c3c0c661016d05c88049ec019d11a1c239320615011d002512040430751a8007c278e8cb400c7cc010d4214986a174bc3a0fee82f08a33f601d26140a0008724552093168ae8017ed8592903b628b3840116866a2071680dc24272d81b9a41c921246c2be805cd0054fc1a2f5053080c740565891aac0bf98275e04f2c1a7552f0600abc0985c145402c398128105490041982e9603490040a204af812312308446b5a043000d6a82135048b411a9805fd833e645836192981fe18374b0c3c011cec329884132019a4995e01e3205fca0c4f60456c09648052449baa148f0217505e9c055fa8d06423192688d0a73e01c880737a2ff245e2892f8018dc048a207e7010228235d818ac0901e0d44c126e3cd0c0bff01aa111c2e80f08031fe186fc075783a6a4cefe8db4c3557829840017a05b691c250cb3a09c348d5ac2939808790af8e9251d2fcb0395209c700b6e003e20293e0419c8be88061402cfa491880249d14ec8626441ed815610276b827ab47b2218bd034fe0217441874045f01bf7846724b8da118bc3283a3bb84bf4613444178003b37000ac069fc2de0a2c7d4712a1371406fd25cd207e2c8e85004428652d0ba3c1726d180da6b5e02c1e0901025240196b471d4106fc1f1f00d550a4580407011508621f0cad8026301cc0231ee03f780efc522a00379304)) else (if i<5 then (if i<4 then 0x2f75a0df940b7a0eeb11ee701c220ac3e176ac25ca03c990a5aa048ac015980c4c03834125d41d7f80b890273a08c31059a8445f02cdc15dd0171c80ac80b99a0fac41bda02f9a09ef28f4dc136480d464c8821780d23f40151a0329403d202ca08634e4104e1ade00ec3a5e2b092de01f7c05b922a0b0135604d881d0f02e710795e036bc201885a5741a980d0f0034585af901ae6036e119020295005f1608f34179da31a80a65a18f640954a460d4740c146bc0142043bb0883c1173c34d42362d0555a0e6e42a9c3cd990493015a7c084d80af94d26c13fc41417016f2052f004e081c4381c3f0ab6c099b0115ba34da4161a07378137a039ff0cab40ebbc04a401e734745e0aec40be18616000d5005da00b3b03a3d0acf80a3741969817a842b628fbcc2c20830324bca408d8008d60525c01d728f364081125c9700db8133ed237f248a4051cc057a41e1a82a110b45a0f99c0e8602923474f20828030a7a67cc0c5509987826bb8625c456881ae88042d84d86082f4196a800622370a46e50094180df70187f069041a5e523c585f2102c4e10f10071e04bc90af321a38010838253603f808200c2cf8a61e40354a90b7925a982d954996c13d48343d85b8b4babe042e02eeb04e63095740ef840f40060850be1a166480ac083c8a0c84012c5010a90435707d14d37fc10c10546403bec98a5833ae862ee0896891d9022b3006b647bda919200a25805d10d69c02ccc0370805e20b12009234147a01b5506f161975c33eb8264c0bcc4134910624a5c2000e9a0805c221101e3e0c2fa18439050886373066b88293c03f2057450d1100c3ec1d88844cf41cac14e1402c403a9345c0211c282e048425f04d360796d1cda0206704e3a0fe141b8888e360ae4e103481623827dc0b2e617ed42acb001e40566206df133fba3d544c13818ed82e088505b46bc603330168a816c64c342066240cee8186806fe6105182fea2403f0476211e980aa6825c7001f61583c19be84da30b7c00a6781c18a487e48bb6930f50552a315b09244181a804b4843f40a23297b182d008342b4681207f7c0fc001d120616a151000a0c809bc0816e0438c0e3883ddc0ceda9287c07ea832740c50404bf02efd237ee046280324825f48434a023da030d116c323ae3073b28e5e43231005590d6ac089b41bbc832e6012660534d3203a0fcf087400b87c00f8a69c00363203f0000d5a5cbc0b4cc0000800b92408c0040202d711d5a835c50013c001911a2f85ab50b2209817c079304d5a039d818cdd2f4e8620a0aaf41a3cc172b23b14490ca0b6051eeca63ff0180c0edac18e9814574c79618ea40c1d8338147da01847420808148441a32181f400c38355248e0a8d7f124b984fa50268a162a914f1a33d702f288a735179a844e44554a0b7e82945205e6397060 else 0x8629a06caa0c5b805960570e0d662033ec11a60670101c40157b00135867b709196074ec1981036ce4d1ee0bc591d92a4807007c814f5c01b3263250c470147181fc981eab0a5fe91a7c3526a68e90445e0d15120f08506c0d5ae8cf800ef1021da0453c066f00d978285f034b8010292e04830cf0099a8d3c80236a37f14cbac1871d358301c4a0c788052f1340384e87056b616f59f55e816300c9bc05c64025fa2e2702b561002ca607833980a29898ed0205205f8c086ec1660005f1060e248d8092aa103d2011d04c0480bfd8142081ca6034108bbd8175180ff8079988ba0809838669e4753c8fc0403ca835b206bee087cc0a11a2a684922a1a9551928035e50af0e156a115930002207a168e570267505124027760e0382b6103df84995415014359081144076f2031a80384045280281a06af403aa00d9b40f60017e532408468008e3e826d41dc522adc07aa0052b42a4f064f50af788fea4274a82a340bd1e0b7b827800613d0769c14b081e03828a803ffa0b2d41f1604fd20a762823b800090323407db8062e82b2e8381e4ca8206eb50040833aa08de813f2011f08066305c42146d81910817394332e82408349d861d90262a82f7822a725dd60368a06f0c073ea3eef4d48c0f7381e38025920346612c9011cb8428e0088a005681b5c0624e0b9cc8da102bd3837a70bcf2068b833e7a2ae9028f60a1cc23f781f780252c06d8811bfa36bb456e00769c0314a438404c6a0e3d91de70188a06c208b0e426278273608c8a06bec2e87864e4027d692fc82155015b40bad401694318303d71484d806e0c17ba83d130b876044b02e9a8132205d1201a7c1b40047c004d1a07bb82c298169006028134dc01fa01f640b17e0b0bd233e839a1047ee0fa40009c058674759209c3c309082001094700fd5810dd8455c41d300a7f030782081f4bbca0643c0b5502fb507ffe13ba52f4704021086de033bc1440024e7463a88d9a81488262db0cd920a0d01d0223146477448ba6117f425ebb4bde6121101618a0f5f04b1a0b42c27c48353c41512828ac13a5825ec024280b6951c1023189043c80053422efa6589098c691c44079b04a8605fcc81e6d1ebf0575b48b3298eb00ded824a4078560bf0806f501ac60a0e013014344fa0c6e0a4380fbcd2de9845e000c82197b02f62829cc006ac91ce92e6485c5e0338818d782d41804760d4ce12c382b71869bd02ef20ee7c1f96053ca055ba816482a658431e007860c3b426a14cd0d0627200b402d658447031fd68ff291b07247b10a1e00686c2a582361701c2611e0d0309060b2021e60182c332a001c70b1180d41c20fd81750410bc064402a7b0333c00b8203bc41abac4cba0a118172cc184fa6274053b20e66c23ad83f7205ebc064f018f4054e601a6e04d6008c6a369f4702812340) else (if i<6 then 0xd0cdbe0ea9d19d48513d4d3529706c1b7281e2e087081482802108260f46b9013cf5343383e7105b9011b482fce05b6841738821b02f2c2375746d46159940b4782f4c0d6d48f46d04c9841240959000dfd300ba358206094133491b9d85ea707b5e0cae815d204e7c09bde1a65c1d10235000009292344244485243096a68f5a4018085ae504fec02448285f8289f4c15812e311dc9a3c1700a2209da830d3056bf085fe19450228c815c40c6ca9096c12f884fbb092161914d3067a0b1e06b50103302ae40181b0c86e077201fa38535d0906a0a07c2eda24a4a06508901b5071200c8941134924f02d9d26a2e4c446821f5e5df814c0011c4057540720030870552001e1922d9820290168a98c112ec6818940a02a100482667a0c5403c280394c1b18035240941097984285600c584168a13fb4259c044974501a0e944221a00fba4678e16a90339510ef203e7011dfc2a19832500428212f682aa506852068cc16fd8194f01ec3041b4923a828fea4b0a09d4e99a3c26ea8536a08ed2985940a9e05006084221341025d384ec10a7c40a41c34b48602d04826925bc1c2ea2bb0058e20524c0aba01c970a33811a7d1fce859b74700c00ec8183c00bba4c1b452e202d1ca5173466ea09888250fa0451080e2029b905670397f054bc025c103ba847f400de0075f52625a43cc02b34084b82a130257d48930152b025b584a7e07b06006451abd853700797a15a180e2f85cae04ad60887c349626af9456a2091f13209a0dd30bf4012a5008b4242240381e18e10015500cbc05a9617ac807680664303908160b8333802bd3078268acf818d220e6c0b1ee0ef5c2a0a807a806cfa1814c32c30632b4650c8f39406e585b0005af619dec08cd230570a0921277c20c782ef801fcc0eb1820a90315e0917e0afa804a923f76498580b25c092384dfd03a888bc8c0c1782a88088d40c9b00e34014640cdfe0d30c202f860910adb498f9410d0818490cffc91df82f6ba335f07c8e0d61c06520107d4991807af404ed838464573292f68355f836f30466492888105a8039d4c018107a427a10654e473041433812a0822070722e0bd81329da4132075bc02730125903a7b08dc21535131e986846475b2105900804a0916025d0027f12fed02ced04cb0157f0089a84270477160f6cc174e868d808cb8123b12057807780738e0288034328306a0223c00bc005b0a2d7b094aa81abc02cba0f01027860cd9d1ce304d9608b088aa151776060d90b7340ac04249d20eda477c402410215ba66d045c7e80ff0096b23ccd45db8824c4298f004120108812258242b8110a0183814eac197c862d50cc5e149b002878678c05290061711add05d5c06b2e18638320d81a460b6888c6f81e68823d04bef6016c82e2580ad7024688f0c926ad816ee0658a997e01f72 else 0x10628283cb80ea9a6aa94d19011208092ca386a0b1bc0f4ec33d784af304e4a000f104e0a39ae003668d2680cc9059a1011ec050f02ca8825d2417c091eb40d32803a403e201927432e68021101430171fc0eb5822f44748a984a01de7802cd482ca10904026c8251041ae408a040076061f84884e1039d1ccd02cc705ac60209412208252505d86132081e78050d90bfca176140ff303dea04eec0c720281e0647e08a0619acc0dfe855d011c82163a91cf7227e14c63e160451b1c848240680a10f402a8b841a5794b20e4e02131260670c15a0c62831fa068c10bc5a021bc05818008c04dd208ea02b1624a9e0cb2a0ec393140229b44d4e0117d01561810500ac780296c165320de00605801cf82ecb83107091fa193102d4b02b740d4448b3c51781a083b4c66019cf9065b05b280623c05930101c260b60422801db80fa486b14093948df5d34db02a270bc9e1a53011c6033c)))
def oH11 (h : Nat) : Option (Nat × Nat):=lookupWord 752 2256 12 19 11 4 oH11F h
def oP12F (i : Nat) : Nat:=(if i<1 then 0xb1ad201e2e0a2503c061e84ed8221280c280a0307b61280c280980095a4018501700143b61640c280dec8f4df9bbc83df6ee4f64bacbd38e8af35394fc5ce0defe3783b94db3ec9b607ab8d31e8db3d79becc3e5432478ecc5ae2230a381abf6dedaeff748b74dacacf7644b0bd782b3f572a8ed34a95f4509fdceea6df324967c9ea47320c8e5c67a2e3130877c38216707c80ebfe9f86f8c7afbc51da6e9273cb931c7ae106f1b6d9ad6d2a67eb3b9982c80615b0497a2b865acac895eaac8548a91946ea1e4f8a71132e96a49ea4691b28ca453a1c10727ee3d19d88e2e6ae3459928bfe5d22e195e0a5a50025a91a882a3ca1bf8cd05e62b212e88c04061f40de861829e11807582d014a0780208003ffd3224520fff54891483ffd8224520fff14c91483ffd5324520fff55091483ffd7424520fff95491483ffd7524520fff21491483ffd8524520fff65491483ffd8724520fffa2091483ffd9824520fff54498483ffd7126120fff4c898483ffd5226120fff14c98483ffd5326120fff55098483ffd7426120fff95498483ffd7526120fff65498483ffd5024d20fff58093483ffd8024d20fff54493483ffd6124d20fff5c493483ffd8124d20fff54893483ffd6224d20fff60893483ffe5524d20fff59493483ffd7524d20fff21493483ffd8524d20fff65493483ffd7624d20fff61893483ffd9624d20fff61c93483ffe8824d20fff66093482ffd5124d20bff60493482ffd9124d20bff54c93482ffd8524d20bff65493482ffd9824d20bffa6493483ff52124520ffd60491483ff59124520ffb88891483fed4224520ffb54891482ffda224520fdf954914837fd9524520bff69491483dfe7724520dff65c91482ffda724520effa20914837fd9824520bff6a0914837fe9924520ffd84498483fed2126120dff244984837fd9126120bff68498483fee2226120ffb50898483fed5226120eff60898482ffda226120fdf954984837fd9526120bff69498483dfe7726120dff65c98482ffda726120eff660984837fe9926120ffe80093483ff91024d20ff74c093483ff97024d20bff68093483ff61124d20ffb484934837fc9124d20dff64493482ffda124d20ffb88893483fdd3224d20ffb54893482ffda224d20ff764c93483f7e5524d20dff254934837fd9524d20bff69493483efe6624d20dff65893482ffda624d20f7f9dc934837fd9724d20bff69c93483bfe8824d20dff260934837fd9824d20bff6a0934837fe9924d20bfd84493482fed2124d209ff64493482fed5224d20bdf954934827fd9524d20affa20934827fd9824d209ffa6493483fe52124520dfd64491482feda224520bdf69491482efda624520b7f69c91482bfda824520cff66098483fd93024d20bfe680934837dd9324d20bbf69893482dfda724d20 else 0xae1060541e148aa45700f0a444183c078522570d484e2911a9f142e6801687ab83a355c03c1a1148469d31781e2e0d5c3aa1a1148ae04a15c8eabe81a0ddfe61d515e1eae0c250880f0a4475452e61485244a178fcc3bfe2d050f1ec61101e1486060da26de80f95d512af407c8a45e80604e409c070780cbd04a35e8ea84e33b86d681d51a60cbd0fe2a46d003f060db7a03c807ef474c1e21dc15f31065e8ea9d47136f47544a204e0f5e8250185ed80112aa0030adb0955007a4ed80112822030a0609a1ed1c0f944d0303f07c8a403e0607a29140c1343da381f287ea403c2911b64183d07852287e830ca0f0a450afb6832a0754a21b70fa07e1ebaadb41950244d522a07544a285632be8ea9d053b9f47560ca80a2507e0f0a445203da81dd128be2b701f87afa54060780c0f45223aa26f6d06292a45402520ee1968ef160c7d0e8387e0f0a430b40c0ba8e81a1a2e0d507d206553471050d4907a03e8aa68eb14b8a600c35bf4111d0356c6ac3473aa8ea0a063d21a354f4140d470195b4346a85080ba8ea0aa986a483d02845534756d2443406188204c1e178925635a41ec5c03e60304a2e01e220c0f0bc06111af14340581e104c293aa1a094145706000383634ead704e603412828ae0a2b85a0f60ceae34251701a2548ae04a1a901a050250bc514b9812859178aefe918d570414bc50d01e15c28ae0e256347b6900f17060b81612ab80780c35e8060bc5e62f403083b07c5e62f40309e2f307a018407948bd00c2331e2b400f8197a03c7079a91280c1caf4303c7a2900610000e0d8d3ab7a11a90784a03072bd0d8303c750958d3aa061e88bd04a13aa26f30065e825184de61c5030593d04a39e82503c0610271281ebd00c2a00255400613c5edaa0030811094470180f15d55204ded80ca804a380c1a800c178bdb54006104a6e2a00309e2f6d500184f17b62800c220c0f0a00610a01400c18a4063aa2507f50180008940f0183edb06c01d5a80bdb0dcea86a061452ed80c7544a0fea03e0d80095db3aa0614077d1b8c03486daa03018253e8db0a41ed4077d00cc03480f4f76d84a2803f5291500943521d51343fa804a309bdb018a40b2500947c03487d2a020c4114bb60306f1283fa80fe2e00fa09432818501fb612aa00308065bf54d1d244345c1edfaa68e032c5868b838196fd53471710d49020a058b7e8ea0ab6868d53dbf475050356d0d1aa7b7e8ea08a9ada1a920f54d1d414907a4346aa68ea08f49221a35056fd53470195b4910d204a12c1e2e08060940f1704000225635a403c5c144ac6b48078b82e34258b20f170512)
def oP12 : Packing:=(143,3,7,0,0,13,0,oP12F)
def oH12F (i : Nat) : Nat:=0x2003a00ef03f544f103ea411507f1079f066d4406061205300764002408ed4565030f06cb067a08164395021302ca06b303c003df052f083405dc44cc47c5074805a4015740ce4857476442ce0471089943fa05e643e803ad453108d006484870086604d105160127482d0323084f001f08a30783019600bc48d947df04a4059f026247544846451f07ac4375009043d945aa082007b804ea072701d401610369452f085d0101444b412c02b948e100ce028606ae08cb43a001cd05430637450405bf03544367486905fb062006fb0385073a077547e24837459403780341056407e101ec44b901a008bb44e50242018340964143088d47f801b041094078005702d6007d44a40571041401f7043140a6055903b6031a017b04c8477e48c2071f02980208046902fd00d507d4022a087706000423040e06d404b802a00450004c06ef014c02e904f643b644df075235eb044d08010236479a00aa05000392008a033c05ca43cd068c0252058d049200f0070e02730694419e0110006c065f0005489d43860485013107c5514000809210000094f001202001c2024042b0e300000020239002a0e0602020e00480002030000000001010f0c0e0501042505050000020018021b113700050000020100000d001600040500000400153c2602340c0d030c000006000f0203000000
def oH12 (h : Nat) : Option (Nat × Nat):=lookupWord 99 197 8 16 8 4 oH12F h
def oP13F (i : Nat) : Nat:=0x2546a901e5c156c14c04941ea446818f4340095b6a40314066faa51c825b12034701046c10c04be10704301954721cd34c1508c38150701c00ffe48a41ffc96483ff928907ff26120ffe49a40ffc93482ff922905ff25920bfe4a2417fc98482ff926901ff24d20
def oP13 : Packing:=(12,2,7,0,0,9,0,oP13F)
def oH13F (i : Nat) : Nat:=0x50250710ad08906d01f0b100c03805409904605900004200
def oH13 (h : Nat) : Option (Nat × Nat):=lookupWord 12 12 4 12 4 4 oH13F h
def oLv : Nat → Packing
  | 7 => oP7
  | 8 => oP8
  | 9 => oP9
  | 10 => oP10
  | 11 => oP11
  | 12 => oP12
  | 13 => oP13
  | _ => emptyPacking
def oIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => oH7
  | 9 => oH8
  | 10 => oH9
  | 11 => oH10
  | 12 => oH11
  | 13 => oH12
  | _ => fun _ => none
def oF : Forest := ⟨511, 13, dead.samples, dead.cols, dead.autos, oLv, oIndex⟩
set_option maxHeartbeats 0 in
theorem c7_0 : block oF 7 0 1=true:=cutsBlock (ar:=7) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c7_1 : block oF 7 1 4=true:=cutsBlock (ar:=8) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c8_0 : block oF 8 0 5=true:=cutsBlock (ar:=8) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c8_5 : block oF 8 5 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c8_69 : block oF 8 69 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c8_133 : block oF 8 133 2=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_0 : block oF 9 0 1=true:=cutsBlock (ar:=8) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1 : block oF 9 1 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_65 : block oF 9 65 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_129 : block oF 9 129 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_193 : block oF 9 193 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_257 : block oF 9 257 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_321 : block oF 9 321 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_385 : block oF 9 385 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_449 : block oF 9 449 15=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_464 : block oF 9 464 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_528 : block oF 9 528 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_592 : block oF 9 592 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_656 : block oF 9 656 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_720 : block oF 9 720 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_784 : block oF 9 784 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_848 : block oF 9 848 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_912 : block oF 9 912 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_976 : block oF 9 976 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1040 : block oF 9 1040 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1104 : block oF 9 1104 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1168 : block oF 9 1168 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1232 : block oF 9 1232 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1296 : block oF 9 1296 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1360 : block oF 9 1360 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1424 : block oF 9 1424 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1488 : block oF 9 1488 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c9_1552 : block oF 9 1552 8=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_0 : block oF 10 0 64=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_64 : block oF 10 64 16=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_80 : block oF 10 80 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_144 : block oF 10 144 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_208 : block oF 10 208 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_272 : block oF 10 272 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_336 : block oF 10 336 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_400 : block oF 10 400 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_464 : block oF 10 464 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_528 : block oF 10 528 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_592 : block oF 10 592 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_656 : block oF 10 656 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_720 : block oF 10 720 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_784 : block oF 10 784 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_848 : block oF 10 848 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_912 : block oF 10 912 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_976 : block oF 10 976 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1040 : block oF 10 1040 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1104 : block oF 10 1104 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1168 : block oF 10 1168 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1232 : block oF 10 1232 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1296 : block oF 10 1296 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1360 : block oF 10 1360 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1424 : block oF 10 1424 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1488 : block oF 10 1488 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1552 : block oF 10 1552 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1616 : block oF 10 1616 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1680 : block oF 10 1680 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1744 : block oF 10 1744 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1808 : block oF 10 1808 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1872 : block oF 10 1872 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1936 : block oF 10 1936 7=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_1943 : block oF 10 1943 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2007 : block oF 10 2007 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2071 : block oF 10 2071 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2135 : block oF 10 2135 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2199 : block oF 10 2199 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2263 : block oF 10 2263 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2327 : block oF 10 2327 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2391 : block oF 10 2391 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2455 : block oF 10 2455 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2519 : block oF 10 2519 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2583 : block oF 10 2583 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2647 : block oF 10 2647 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2711 : block oF 10 2711 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2775 : block oF 10 2775 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2839 : block oF 10 2839 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2903 : block oF 10 2903 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_2967 : block oF 10 2967 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3031 : block oF 10 3031 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3095 : block oF 10 3095 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3159 : block oF 10 3159 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3223 : block oF 10 3223 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3287 : block oF 10 3287 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3351 : block oF 10 3351 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3415 : block oF 10 3415 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3479 : block oF 10 3479 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3543 : block oF 10 3543 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3607 : block oF 10 3607 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3671 : block oF 10 3671 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3735 : block oF 10 3735 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3799 : block oF 10 3799 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3863 : block oF 10 3863 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3927 : block oF 10 3927 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_3991 : block oF 10 3991 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c10_4055 : block oF 10 4055 16=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_0 : block oF 11 0 2=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_2 : block oF 11 2 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_66 : block oF 11 66 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_130 : block oF 11 130 64=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_194 : block oF 11 194 62=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_256 : block oF 11 256 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_320 : block oF 11 320 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_384 : block oF 11 384 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_448 : block oF 11 448 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_512 : block oF 11 512 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_576 : block oF 11 576 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_640 : block oF 11 640 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_704 : block oF 11 704 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_768 : block oF 11 768 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_832 : block oF 11 832 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_896 : block oF 11 896 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_960 : block oF 11 960 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1024 : block oF 11 1024 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1088 : block oF 11 1088 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1152 : block oF 11 1152 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1216 : block oF 11 1216 42=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1258 : block oF 11 1258 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1322 : block oF 11 1322 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1386 : block oF 11 1386 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1450 : block oF 11 1450 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1514 : block oF 11 1514 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1578 : block oF 11 1578 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1642 : block oF 11 1642 64=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c11_1706 : block oF 11 1706 18=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c12_0 : block oF 12 0 22=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c12_22 : block oF 12 22 64=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c12_86 : block oF 12 86 9=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c12_95 : block oF 12 95 48=true:=cutsBlock (ar:=12) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c13_0 : block oF 13 0 1=true:=cutsBlock (ar:=9) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c13_1 : block oF 13 1 6=true:=cutsBlock (ar:=10) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c13_7 : block oF 13 7 5=true:=cutsBlock (ar:=11) (by decide +kernel) (by decide +kernel)
theorem a7 : block oF 7 0 5=true:=(@block_merge oF 7 0 1 4 c7_0 c7_1)
theorem a8 : block oF 8 0 135=true:=(@block_merge oF 8 0 69 66 (@block_merge oF 8 0 5 64 c8_0 c8_5) (@block_merge oF 8 69 64 2 c8_69 c8_133))
theorem a9 : block oF 9 0 1560=true:=(@block_merge oF 9 0 720 840 (@block_merge oF 9 0 321 399 (@block_merge oF 9 0 129 192 (@block_merge oF 9 0 1 128 c9_0 (@block_merge oF 9 1 64 64 c9_1 c9_65)) (@block_merge oF 9 129 64 128 c9_129 (@block_merge oF 9 193 64 64 c9_193 c9_257))) (@block_merge oF 9 321 143 256 (@block_merge oF 9 321 64 79 c9_321 (@block_merge oF 9 385 64 15 c9_385 c9_449)) (@block_merge oF 9 464 128 128 (@block_merge oF 9 464 64 64 c9_464 c9_528) (@block_merge oF 9 592 64 64 c9_592 c9_656)))) (@block_merge oF 9 720 448 392 (@block_merge oF 9 720 192 256 (@block_merge oF 9 720 64 128 c9_720 (@block_merge oF 9 784 64 64 c9_784 c9_848)) (@block_merge oF 9 912 128 128 (@block_merge oF 9 912 64 64 c9_912 c9_976) (@block_merge oF 9 1040 64 64 c9_1040 c9_1104))) (@block_merge oF 9 1168 192 200 (@block_merge oF 9 1168 64 128 c9_1168 (@block_merge oF 9 1232 64 64 c9_1232 c9_1296)) (@block_merge oF 9 1360 128 72 (@block_merge oF 9 1360 64 64 c9_1360 c9_1424) (@block_merge oF 9 1488 64 8 c9_1488 c9_1552)))))
theorem a10 : block oF 10 0 4071=true:=(@block_merge oF 10 0 2007 2064 (@block_merge oF 10 0 976 1031 (@block_merge oF 10 0 464 512 (@block_merge oF 10 0 208 256 (@block_merge oF 10 0 80 128 (@block_merge oF 10 0 64 16 c10_0 c10_64) (@block_merge oF 10 80 64 64 c10_80 c10_144)) (@block_merge oF 10 208 128 128 (@block_merge oF 10 208 64 64 c10_208 c10_272) (@block_merge oF 10 336 64 64 c10_336 c10_400))) (@block_merge oF 10 464 256 256 (@block_merge oF 10 464 128 128 (@block_merge oF 10 464 64 64 c10_464 c10_528) (@block_merge oF 10 592 64 64 c10_592 c10_656)) (@block_merge oF 10 720 128 128 (@block_merge oF 10 720 64 64 c10_720 c10_784) (@block_merge oF 10 848 64 64 c10_848 c10_912)))) (@block_merge oF 10 976 512 519 (@block_merge oF 10 976 256 256 (@block_merge oF 10 976 128 128 (@block_merge oF 10 976 64 64 c10_976 c10_1040) (@block_merge oF 10 1104 64 64 c10_1104 c10_1168)) (@block_merge oF 10 1232 128 128 (@block_merge oF 10 1232 64 64 c10_1232 c10_1296) (@block_merge oF 10 1360 64 64 c10_1360 c10_1424))) (@block_merge oF 10 1488 256 263 (@block_merge oF 10 1488 128 128 (@block_merge oF 10 1488 64 64 c10_1488 c10_1552) (@block_merge oF 10 1616 64 64 c10_1616 c10_1680)) (@block_merge oF 10 1744 128 135 (@block_merge oF 10 1744 64 64 c10_1744 c10_1808) (@block_merge oF 10 1872 64 71 c10_1872 (@block_merge oF 10 1936 7 64 c10_1936 c10_1943)))))) (@block_merge oF 10 2007 1024 1040 (@block_merge oF 10 2007 512 512 (@block_merge oF 10 2007 256 256 (@block_merge oF 10 2007 128 128 (@block_merge oF 10 2007 64 64 c10_2007 c10_2071) (@block_merge oF 10 2135 64 64 c10_2135 c10_2199)) (@block_merge oF 10 2263 128 128 (@block_merge oF 10 2263 64 64 c10_2263 c10_2327) (@block_merge oF 10 2391 64 64 c10_2391 c10_2455))) (@block_merge oF 10 2519 256 256 (@block_merge oF 10 2519 128 128 (@block_merge oF 10 2519 64 64 c10_2519 c10_2583) (@block_merge oF 10 2647 64 64 c10_2647 c10_2711)) (@block_merge oF 10 2775 128 128 (@block_merge oF 10 2775 64 64 c10_2775 c10_2839) (@block_merge oF 10 2903 64 64 c10_2903 c10_2967)))) (@block_merge oF 10 3031 512 528 (@block_merge oF 10 3031 256 256 (@block_merge oF 10 3031 128 128 (@block_merge oF 10 3031 64 64 c10_3031 c10_3095) (@block_merge oF 10 3159 64 64 c10_3159 c10_3223)) (@block_merge oF 10 3287 128 128 (@block_merge oF 10 3287 64 64 c10_3287 c10_3351) (@block_merge oF 10 3415 64 64 c10_3415 c10_3479))) (@block_merge oF 10 3543 256 272 (@block_merge oF 10 3543 128 128 (@block_merge oF 10 3543 64 64 c10_3543 c10_3607) (@block_merge oF 10 3671 64 64 c10_3671 c10_3735)) (@block_merge oF 10 3799 128 144 (@block_merge oF 10 3799 64 64 c10_3799 c10_3863) (@block_merge oF 10 3927 64 80 c10_3927 (@block_merge oF 10 3991 64 16 c10_3991 c10_4055)))))))
theorem a11 : block oF 11 0 1724=true:=(@block_merge oF 11 0 832 892 (@block_merge oF 11 0 384 448 (@block_merge oF 11 0 130 254 (@block_merge oF 11 0 2 128 c11_0 (@block_merge oF 11 2 64 64 c11_2 c11_66)) (@block_merge oF 11 130 126 128 (@block_merge oF 11 130 64 62 c11_130 c11_194) (@block_merge oF 11 256 64 64 c11_256 c11_320))) (@block_merge oF 11 384 192 256 (@block_merge oF 11 384 64 128 c11_384 (@block_merge oF 11 448 64 64 c11_448 c11_512)) (@block_merge oF 11 576 128 128 (@block_merge oF 11 576 64 64 c11_576 c11_640) (@block_merge oF 11 704 64 64 c11_704 c11_768)))) (@block_merge oF 11 832 426 466 (@block_merge oF 11 832 192 234 (@block_merge oF 11 832 64 128 c11_832 (@block_merge oF 11 896 64 64 c11_896 c11_960)) (@block_merge oF 11 1024 128 106 (@block_merge oF 11 1024 64 64 c11_1024 c11_1088) (@block_merge oF 11 1152 64 42 c11_1152 c11_1216))) (@block_merge oF 11 1258 256 210 (@block_merge oF 11 1258 128 128 (@block_merge oF 11 1258 64 64 c11_1258 c11_1322) (@block_merge oF 11 1386 64 64 c11_1386 c11_1450)) (@block_merge oF 11 1514 128 82 (@block_merge oF 11 1514 64 64 c11_1514 c11_1578) (@block_merge oF 11 1642 64 18 c11_1642 c11_1706)))))
theorem a12 : block oF 12 0 143=true:=(@block_merge oF 12 0 86 57 (@block_merge oF 12 0 22 64 c12_0 c12_22) (@block_merge oF 12 86 9 48 c12_86 c12_95))
theorem a13 : block oF 13 0 12=true:=(@block_merge oF 13 0 1 11 c13_0 (@block_merge oF 13 1 6 5 c13_1 c13_7))
theorem oChecked : checkedTables oF 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block oF 0 0 0 = true)
  · exact (rfl : block oF 1 0 0 = true)
  · exact (rfl : block oF 2 0 0 = true)
  · exact (rfl : block oF 3 0 0 = true)
  · exact (rfl : block oF 4 0 0 = true)
  · exact (rfl : block oF 5 0 0 = true)
  · exact (rfl : block oF 6 0 0 = true)
  · exact a7
  · exact a8
  · exact a9
  · exact a10
  · exact a11
  · exact a12
  · exact a13

def ySig : Sig := bin true (inputs.getD 0 zero) (inputs.getD 2 zero)
def zSig (a : Nat) : Sig := bin false (inputs.getD a zero) ySig
def rootsYZ (a : Nat) : List Sig := inputs ++ [ySig, zSig a]
def rootsZ (a : Nat) : List Sig := inputs ++ [zSig a]
def rootsY : List Sig := inputs ++ [ySig]
def pinSet : List Nat := [1,3,4,6,8]
def rootIdx (a : Nat) (withY : Bool) : Nat :=
  if withY then (if a = 3 then 7 else if a = 8 then 8 else if a = 4 then 9 else if a = 6 then 10 else 11) else (if a = 3 then 1 else if a = 8 then 2 else if a = 4 then 3 else if a = 6 then 4 else 5)
theorem geomOF : graphValid oF (boundsBefore known383) = true := geomdead
theorem oAll : ∀ k ≤ 13, ∀ i < (oF.levels k).1, Impossible (targetOf oF) k (stateSet oF k i).toFinset :=
  forest_all oF 13 (boundsBefore known383) (before_sound known383 valid383) geomOF oChecked
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tgtOF : targetOf oF = graph := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rootMatch : (∀ a ∈ pinSet, (rootIdx a true < (oF.levels 13).1 ∧ rootIdx a false < (oF.levels 13).1) ∧
    sameWords (stateSet oF 13 (rootIdx a true)) (rootsYZ a) = true ∧
    sameWords (stateSet oF 13 (rootIdx a false)) (rootsZ a) = true) ∧
    (6 < (oF.levels 13).1 ∧ sameWords (stateSet oF 13 6) rootsY = true) ∧
    (0 < (oF.levels 13).1 ∧ sameWords (stateSet oF 13 0) inputs = true) := by decide +kernel
theorem impOf {i : Nat} {ws : List Sig} (hi : i < (oF.levels 13).1) (hs : sameWords (stateSet oF 13 i) ws = true) :
    Impossible graph 13 ws.toFinset := by
  have h := oAll 13 le_rfl i hi
  rw [tgtOF, sameWords_sound hs] at h
  exact h
def witRows (a : Nat) : List (Nat × Nat) :=
  if a = 1 then [(20,21),(64,66),(9,13),(4,12),(1,17),(1,33),(2,66),(4,132),(8,264)] else if a = 3 then [(20,21),(1,3),(9,13),(16,24),(1,17),(1,33),(2,66),(4,132),(8,264)] else if a = 4 then [(20,21),(1,3),(9,13),(4,12),(8,24),(1,33),(2,66),(4,132),(8,264)]
  else if a = 6 then [(20,21),(1,3),(9,13),(4,12),(1,17),(1,33),(2,66),(4,132),(8,264)] else [(20,21),(1,3),(9,13),(4,12),(1,17),(1,33),(2,66),(4,132),(8,264)]
def wr (a i : Nat) : Row × Row := ((Fin.ofNat 512 ((witRows a).getD i (0,0)).1), (Fin.ofNat 512 ((witRows a).getD i (0,0)).2))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem witOK : ∀ a ∈ pinSet, ∀ i : Fin 9,
    (bit (wr a i.val).1 graph != bit (wr a i.val).2 graph) &&
    ((rootsYZ a).all fun w => w == inputs.getD i.val zero || bit (wr a i.val).1 w == bit (wr a i.val).2 w) = true := by
  decide +kernel
theorem inputs_in (a : Nat) (ha : a ∈ pinSet) {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ rootsYZ a) :
    inputs.toFinset ⊆ S := by
  intro v hv
  have hm := List.mem_toFinset.mp hv
  rw [←input_list,List.mem_ofFn] at hm
  obtain ⟨i,rfl⟩ := hm
  have cut := witOK a ha i
  simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
    Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
  apply raw_required h _ _ sub (wr a i.val).1 (wr a i.val).2 cut.1
  exact fun w hw hne => (cut.2 w hw).resolve_left hne
theorem noLive (a : Nat) (ha : a ∈ pinSet) {k t S} (h : Live graph k t S) (hk : k ≤ 13)
    (sub : ∀ v ∈ S, v ∈ rootsYZ a) : False := by
  classical
  have hin := inputs_in a ha h sub
  have m := rootMatch
  have hm := m.1 a ha
  have memS : ∀ w, w ∈ S ↔ (w ∈ inputs ∨ (w = ySig ∧ ySig ∈ S) ∨ (w = zSig a ∧ zSig a ∈ S)) := by
    intro w; constructor
    · intro hw
      have hx := sub w hw
      simp only [rootsYZ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl
      · exact Or.inl hx
      · exact Or.inr (Or.inl ⟨rfl, hw⟩)
      · exact Or.inr (Or.inr ⟨rfl, hw⟩)
    · rintro (hx | ⟨rfl, hy⟩ | ⟨rfl, hz⟩)
      · exact hin (List.mem_toFinset.mpr hx)
      · exact hy
      · exact hz
  by_cases hy : ySig ∈ S <;> by_cases hz : zSig a ∈ S
  · have e : S = (rootsYZ a).toFinset := by
      ext w; rw [memS w]; simp [rootsYZ, hy, hz] <;> first | exact or_comm.trans or_assoc | exact or_comm | rfl
    exact impOf hm.1.1 hm.2.1 k t hk (e ▸ h)
  · have e : S = rootsY.toFinset := by
      ext w; rw [memS w]; simp [rootsY, hy, hz] <;> first | exact or_comm.trans or_assoc | exact or_comm | rfl
    exact impOf m.2.1.1 m.2.1.2 k t hk (e ▸ h)
  · have e : S = (rootsZ a).toFinset := by
      ext w; rw [memS w]; simp [rootsZ, hy, hz] <;> first | exact or_comm.trans or_assoc | exact or_comm | rfl
    exact impOf hm.1.2 hm.2.2 k t hk (e ▸ h)
  · have e : S = inputs.toFinset := by
      ext w; rw [memS w]; simp [hy, hz] <;> first | exact or_comm.trans or_assoc | exact or_comm | rfl
    exact impOf m.2.2.1 m.2.2.2 k t hk (e ▸ h)
def gOr : Gate := ⟨GateOp.or, [0,2]⟩
def gAnd (a : Nat) : Gate := ⟨GateOp.and, [a, 9]⟩
def wrapC (C : Circuit) (a : Nat) : Circuit := ⟨gOr :: gAnd a :: C.gates, C.output⟩
theorem wrap_wires (C : Circuit) (a : Nat) (x : List Bool) :
    (wrapC C a).wires x = C.wires (x ++ [GateOp.or.eval ([0,2].map fun i => x.getD i false)] ++
      [GateOp.and.eval ([a,9].map fun i => (x ++ [GateOp.or.eval ([0,2].map fun i => x.getD i false)]).getD i false)]) := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem gv_or : gv inputs gOr = ySig := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem gv_and : ∀ a ∈ pinSet, gv (inputs ++ [ySig]) (gAnd a) = zSig a := by decide +kernel
theorem graph_mem (C : Circuit) (a : Nat) (ha : a ∈ pinSet) (hfanD : PEqualNP.MetaComplexity.FanInTwo (wrapC C a))
    (hD : ∀ x : Fin 9 → Bool, (wrapC C a).eval (List.ofFn x) = edge x) :
    graph ∈ execute C.gates (rootsYZ a) := by
  have goalEq : (execute (wrapC C a).gates inputs).getD (wrapC C a).output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval (wrapC C a) hfanD (wrapC C a).output r).trans ((hD (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute (wrapC C a).gates inputs) (wrapC C a).output
  rw [goalEq] at out
  have hmem := out.resolve_right (fun hn => hn graph_proper)
  have hex : execute (wrapC C a).gates inputs = execute C.gates (rootsYZ a) := by
    change execute C.gates ((inputs ++ [gv inputs gOr]) ++ [gv (inputs ++ [gv inputs gOr]) (gAnd a)]) = _
    rw [gv_or, gv_and a ha]
    simp [rootsYZ]
  rw [hex] at hmem
  exact hmem
theorem fromCircuit (a : Fin 11) (ha : a.val ∈ pinSet) (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 13)
    (hc : ∀ x6 : Fin 9 → Bool, (have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];
      C.eval (x7 ++ [GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) [a, (9 : Fin (11 : ℕ))])]) = edge x6)) :
    False := by
  have hD : ∀ x : Fin 9 → Bool, (wrapC C a.val).eval (List.ofFn x) = edge x := by
    intro x
    rw [← hc x]
    unfold Circuit.eval
    rw [wrap_wires]
    change (C.wires _).getD C.output false = (C.wires _).getD C.output false
    congr 3
    · simp [GateOp.eval, List.getD_eq_getElem?_getD]
    · simp [GateOp.eval, List.getD_eq_getElem?_getD]
  have hfanD : PEqualNP.MetaComplexity.FanInTwo (wrapC C a.val) := by
    intro g hg
    simp only [wrapC, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [gOr]
    · simp [gAnd]
    · exact hfan g hg
  have hout := graph_mem C a.val ha hfanD hD
  have legal : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := hfan
  obtain ⟨k,t,S,hk,run,hsub⟩ := extract C.gates (rootsYZ a.val) legal graph_proper hout
  have hlen : C.gates.length ≤ 13 := hs
  exact noLive a.val ha run (by omega) hsub

end PEqualNP.Outside.L_meta_3913_aux

open PEqualNP.Outside.L_meta_3913_aux in
theorem PEqualNP.Outside.L_meta_3913 :
    ∀ x1 ∈ [[(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 C hfan hsize
  by_contra hne
  have key : ∀ (a : Fin 11), a.val ∈ pinSet → x1 = [a, (9 : Fin (11 : ℕ))] → False := fun a ha hx => by
    subst hx
    exact fromCircuit a ha C hfan hsize (fun x6 => by_contra (fun h => hne ⟨x6, h⟩))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
  rcases hx1 with h | h | h | h | h
  · exact key 1 (by decide) h
  · exact key 3 (by decide) h
  · exact key 4 (by decide) h
  · exact key 6 (by decide) h
  · exact key 8 (by decide) h
