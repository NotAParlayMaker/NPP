import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- Certificates by odinfree, public PR 5789, revision 97f2ca4257bd6727e0f375b699012bebe0f9be33.
-- This specialization checks the positive input pin only.
namespace PEqualNP.Outside.L_meta_3178
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero:Sig:=0
def one:Sig:=BitVec.allOnes 512
def neg (a:Sig):Sig:= ~~~a
def bin (d:Bool) (a b:Sig):Sig:=if d then a ||| b else a &&& b
def proper (a:Sig):Prop:=a ≠ zero ∧ a ≠ one
theorem bin_comm (d:Bool) (a b:Sig):bin d a b = bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (tgt:Sig) (k t:Nat) (S:Finset Sig):Prop :=
  ∀ P:Nat → Nat → Finset Sig → Prop,
    (∀ (hp:proper tgt),P 0 0 {tgt}) →
    (∀ {k t:Nat} {U:Finset Sig} {a:Sig} (ha:proper a) (hfresh:neg a ∉ insert a U) (tail:P k t (insert (neg a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (ha:proper a) (hb:proper b) (hab:a ≠ b) (hfresh:bin d a b ∉ insert a (insert b U)) (tail:P k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) →
    P k t S
theorem Live.stop {tgt:Sig}  (hp:proper tgt):Live tgt 0 0 {tgt}:=by
  intro P cstop cunary cbinary
  exact cstop hp
theorem Live.unary {tgt:Sig} {k t:Nat} {U:Finset Sig} {a:Sig} (ha:proper a) (hfresh:neg a ∉ insert a U) (tail:Live tgt k t (insert (neg a) U)):Live tgt (k+1) (t+1) (insert a U):=by
  intro P cstop cunary cbinary
  exact cunary ha hfresh (tail P cstop cunary cbinary)
theorem Live.binary {tgt:Sig} {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (ha:proper a) (hb:proper b) (hab:a ≠ b) (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live tgt k t (insert (bin d a b) U)):Live tgt (k+1) t (insert a (insert b U)):=by
  intro P cstop cunary cbinary
  exact cbinary ha hb hab hfresh (tail P cstop cunary cbinary)
theorem Live.elimP {tgt:Sig} {motive:∀ (k t:Nat) (S:Finset Sig),Live tgt k t S → Prop}
    (stop:∀ (hp:proper tgt),motive 0 0 {tgt} (Live.stop hp))
    (unary:∀ {k t:Nat} {U:Finset Sig} {a:Sig} (ha:proper a) (hfresh:neg a ∉ insert a U) (tail:Live tgt k t (insert (neg a) U)) (ih:motive k t (insert (neg a) U) tail),motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary:∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (ha:proper a) (hb:proper b) (hab:a ≠ b) (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live tgt k t (insert (bin d a b) U)) (ih:motive k t (insert (bin d a b) U) tail),motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t:Nat} {S:Finset Sig} (h:Live tgt k t S):motive k t S h:=by
  obtain ⟨hother,hm⟩:=h (fun k t S => ∃ hh:Live tgt k t S,motive k t S hh)
    (fun hp => ⟨Live.stop hp,stop hp⟩)
    (fun ha hfresh ⟨ht,hi⟩ => ⟨Live.unary ha hfresh ht,unary ha hfresh ht hi⟩)
    (fun ha hb hab hfresh ⟨ht,hi⟩ => ⟨Live.binary ha hb hab hfresh ht,binary ha hb hab hfresh ht hi⟩)
  exact hm
lemma live_proper {k t S} (h:Live tgt k t S):∀ a ∈ S,proper a:=by
  induction h using Live.elimP with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h:Live tgt k t S):t ≤ k ∧ S.card+t ≤ k+1:=by
  induction h using Live.elimP with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu:neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu:bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def gv (w:List Sig) (g:Gate):Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs:List Gate) (w:List Sig):List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w:List Sig) (v:Sig):Prop:=v ∈ w ∨ ¬proper v
lemma get_rep (w:List Sig) (i:Nat):represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h:w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma bin_laws (a:Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
lemma neg_laws:neg zero = one ∧ neg one = zero:=by simp [neg,zero,one]
lemma operand_cases {w:List Sig} {a:Sig} (h:represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a:=by
  by_cases hz:a = zero
  · exact Or.inl hz
  by_cases ho:a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w:List Sig) (z:Sig):Prop :=
  (∃ a ∈ w,proper a ∧ z = neg a) ∨
  (∃ d a b,a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d:Bool) (ha:represented w a) (hb:represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b):=by
  have rz:represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro:represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he:a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
lemma gate_rep (w:List Sig) (g:Gate)
    (h:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩:=h
  have rz:represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro:represented w one:=Or.inr (fun h => h.2 rfl)
  have nx (a:Sig) (ha:represented w a):represented w (neg a) ∨ witness w (neg a):=by
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
lemma pull_gate {w:List Sig} {z:Sig} {k t S} (h:Live tgt k t S)
    (hz:represented w z ∨ witness w z) (sub:∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1 ∧ Live tgt k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  by_cases hm:z ∈ S
  · by_cases hw:z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu:a ∈ w ∨ a = z:=by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (neg a)
        have ht:Live tgt k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu:∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf:neg a ∉ insert a U:=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (bin d a b)
        have ht:Live tgt k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu:∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf:bin d a b ∉ insert a (insert b U):=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn:a ≠ z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
lemma extract (gs:List Gate) (w:List Sig)
    (legal:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2)
    (hp:proper tgt) (hout:tgt ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length ∧ Live tgt k t S ∧ ∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{tgt},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩:=pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩
def bit (i:Fin 512) (a:Sig):Bool:=a.getLsbD i.val
lemma bit_zero (i):bit i zero = false:=by simp [bit,zero]
lemma bit_one (i):bit i one = true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a:Sig):bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b:Sig):bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b):=by cases d <;> simp [bit,bin]
lemma b_read (i) (w:List Sig) (j:Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
lemma run_bit (i) (g:Gate) (w:List Sig)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩:=g
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
lemma execute_bits (gs:List Gate) (i) (w:List Sig)
    (hg:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l:List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R:Type):=R → Bool
def inv {R} (a:Wire R):Wire R:=fun r => !(a r)
def combine {R} (isOr:Bool) (a b:Wire R):Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a:Wire R):Prop:=∃ b:Bool,a = fun _ => b
noncomputable def cost {R} (a:Wire R):Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs:List (Wire R)):Nat:=(xs.map cost).sum
def z7 {R} (pool:List (Wire R)) (v:Wire R):Prop:=v ∈ pool ∨ Constant v
def supply {R} (pool xs:List (Wire R)):=∀ a ∈ xs,z7 pool a
def Reach {R:Type} (rr:List (Wire R)) (p:Nat) (bk:List (Wire R)):Prop :=
  ∀ P:Nat → List (Wire R) → Prop,
    (P 0 rr) →
    (∀ {p bk a} (tail:P p bk) (ha:z7 bk a),P (p+1) (inv a :: bk)) →
    (∀ {p bk a b} (op:Bool) (tail:P p bk) (ha:z7 bk a) (hb:z7 bk b),P (p+1) (combine op a b :: bk)) →
    P p bk
theorem Reach.start {R:Type} {rr:List (Wire R)}  :Reach rr 0 rr:=by
  intro P cstart cone ctwo
  exact cstart
theorem Reach.one {R:Type} {rr:List (Wire R)} {p bk a} (tail:Reach rr p bk) (ha:z7 bk a):Reach rr (p+1) (inv a :: bk):=by
  intro P cstart cone ctwo
  exact cone (tail P cstart cone ctwo) ha
theorem Reach.two {R:Type} {rr:List (Wire R)} {p bk a b} (op:Bool) (tail:Reach rr p bk) (ha:z7 bk a) (hb:z7 bk b):Reach rr (p+1) (combine op a b :: bk):=by
  intro P cstart cone ctwo
  exact ctwo op (tail P cstart cone ctwo) ha hb
theorem Reach.elimP {R:Type} {rr:List (Wire R)} {motive:∀ (p:Nat) (bk:List (Wire R)),Reach rr p bk → Prop}
    (start:motive 0 rr (Reach.start ))
    (one:∀ {p bk a} (tail:Reach rr p bk) (ha:z7 bk a) (ih:motive p bk tail),motive (p+1) (inv a :: bk) (Reach.one tail ha))
    (two:∀ {p bk a b} (op:Bool) (tail:Reach rr p bk) (ha:z7 bk a) (hb:z7 bk b) (ih:motive p bk tail),motive (p+1) (combine op a b :: bk) (Reach.two op tail ha hb))
    {p:Nat} {bk:List (Wire R)} (h:Reach rr p bk):motive p bk h:=by
  obtain ⟨hother,hm⟩:=h (fun p bk => ∃ hh:Reach rr p bk,motive p bk hh)
    (⟨Reach.start ,start ⟩)
    (fun ⟨ht,hi⟩ ha => ⟨Reach.one ht ha,one ht ha hi⟩)
    (fun op ⟨ht,hi⟩ ha hb => ⟨Reach.two op ht ha hb,two op ht ha hb hi⟩)
  exact hm
def kept {α:Type} (save:Bool) (x:α) (xs:List α):=if save then x::xs else xs
def Run {R:Type} (goal:Wire R) (s:Nat) (xs:List (Wire R)):Prop :=
  ∀ P:Nat → List (Wire R) → Prop,
    (P 0 [goal]) →
    (∀ {s:Nat} {xs zs:List (Wire R)} (hp:xs.Perm zs) (tail:P s xs),P s zs) →
    (∀ {s a rest} (save:Bool) (tail:P s (inv a :: kept save a rest)),P (s+1) (a::rest)) →
    (∀ {s a b rest} (op ka kb:Bool) (tail:P s (combine op a b :: kept ka a (kept kb b rest))),P (s+1) (a::b::rest)) →
    P s xs
theorem Run.stop {R:Type} {goal:Wire R}  :Run goal 0 [goal]:=by
  intro P cstop cperm cone ctwo
  exact cstop
theorem Run.perm {R:Type} {goal:Wire R} {s:Nat} {xs zs:List (Wire R)} (hp:xs.Perm zs) (tail:Run goal s xs):Run goal s zs:=by
  intro P cstop cperm cone ctwo
  exact cperm hp (tail P cstop cperm cone ctwo)
theorem Run.one {R:Type} {goal:Wire R} {s a rest} (save:Bool) (tail:Run goal s (inv a :: kept save a rest)):Run goal (s+1) (a::rest):=by
  intro P cstop cperm cone ctwo
  exact cone save (tail P cstop cperm cone ctwo)
theorem Run.two {R:Type} {goal:Wire R} {s a b rest} (op ka kb:Bool) (tail:Run goal s (combine op a b :: kept ka a (kept kb b rest))):Run goal (s+1) (a::b::rest):=by
  intro P cstop cperm cone ctwo
  exact ctwo op ka kb (tail P cstop cperm cone ctwo)
theorem Run.elimP {R:Type} {goal:Wire R} {motive:∀ (s:Nat) (xs:List (Wire R)),Run goal s xs → Prop}
    (stop:motive 0 [goal] (Run.stop ))
    (perm:∀ {s:Nat} {xs zs:List (Wire R)} (hp:xs.Perm zs) (tail:Run goal s xs) (ih:motive s xs tail),motive s zs (Run.perm hp tail))
    (one:∀ {s a rest} (save:Bool) (tail:Run goal s (inv a :: kept save a rest)) (ih:motive s (inv a :: kept save a rest) tail),motive (s+1) (a::rest) (Run.one save tail))
    (two:∀ {s a b rest} (op ka kb:Bool) (tail:Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih:motive s (combine op a b :: kept ka a (kept kb b rest)) tail),motive (s+1) (a::b::rest) (Run.two op ka kb tail))
    {s:Nat} {xs:List (Wire R)} (h:Run goal s xs):motive s xs h:=by
  obtain ⟨hother,hm⟩:=h (fun s xs => ∃ hh:Run goal s xs,motive s xs hh)
    (⟨Run.stop ,stop ⟩)
    (fun hp ⟨ht,hi⟩ => ⟨Run.perm hp ht,perm hp ht hi⟩)
    (fun save ⟨ht,hi⟩ => ⟨Run.one save ht,one save ht hi⟩)
    (fun op ka kb ⟨ht,hi⟩ => ⟨Run.two op ka kb ht,two op ka kb ht hi⟩)
  exact hm
theorem mass_cons {R} (a:Wire R) (xs):mass (a::xs)=cost a + mass xs:=by
  simp [mass]
theorem mass_kept {R} (a:Wire R) (xs) (k:Bool):mass xs ≤ mass (kept k a xs):=by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a:Wire R} (h:Constant a):Constant (inv a):=by
  obtain ⟨v,rfl⟩:=h
  exact ⟨!v,rfl⟩
theorem both_constant {R} {a b:Wire R} (op) (h:Constant a) (g:Constant b) :
    Constant (combine op a b):=by
  obtain ⟨v,rfl⟩:=h
  obtain ⟨w,rfl⟩:=g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R} (op) {a b:Wire R} {bk}
    (h:Constant a ∨ Constant b) (ha:z7 bk a) (hb:z7 bk b) :
    z7 bk (combine op a b):=by
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
theorem available_cons {R} {bk v} (w:Wire R) (h:z7 bk v) :
    z7 (w::bk) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (rr:List (Wire R)) {p bk a} (hp:Reach rr p bk)
    (ha:z7 bk a) :
    ∃ q next,Reach rr q next ∧ z7 next (inv a) ∧
        (∀ v,z7 bk v → z7 next v) ∧ q+cost a ≤ p+1+cost (inv a):=by
  classical
  by_cases c:Constant a
  · exact ⟨p,bk,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩
theorem extend_two {R} (rr:List (Wire R)) {p bk a b} (op) (hp:Reach rr p bk)
    (ha:z7 bk a) (hb:z7 bk b) :
    ∃ q next,Reach rr q next ∧ z7 next (combine op a b) ∧
        (∀ v,z7 bk v → z7 next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b):=by
  classical
  by_cases c:Constant a ∨ Constant b
  · refine ⟨p,bk,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca:Constant a <;> by_cases cb:Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca:¬Constant a:=fun h => c (Or.inl h)
    have cb:¬Constant b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem mem_kept {α:Type} {k:Bool} {x a:α} {xs} (h:x ∈ kept k a xs) :
    x=a ∨ x∈xs:=by cases k <;> simp_all [kept]
theorem contraction {R} {goal:Wire R} (nc:¬Constant goal) {s ws}
    (h:Run goal s ws) (rr:List (Wire R)) {p bk}
    (hp:Reach rr p bk) (hs:supply bk ws) :
    ∃ q next,Reach rr q next ∧ z7 next goal ∧ q+mass ws ≤ p+s:=by
  classical
  induction h using Run.elimP generalizing p bk with
  | stop =>
    exact ⟨p,bk,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub:supply bk _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_one rr hp (hs a (by simp))
    have ht:supply T (inv a :: kept save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_two rr op hp (hs a (by simp)) (hs b (by simp))
    have ht:supply T (combine op a b :: kept ka a (kept kb b rest)):=by
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
def z3 {R S:Type} (rows:S → R) (a:Wire R):Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S:Type} (rows:S → R) (k:Bool) (a:Wire R) (ws) :
    (kept k a ws).map (z3 rows) =
    kept k (z3 rows a) (ws.map (z3 rows)):=by
  cases k <;> simp [kept]
theorem restrict_run {R S:Type} (rows:S → R) {goal s ws} (h:Run goal s ws) :
    Run (z3 rows goal) s (ws.map (z3 rows)):=by
  induction h using Run.elimP with
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
theorem projected_bound {R S:Type} (rows:S → R) {goal s ws} (h:Run goal s ws)
    (nc:¬Constant (z3 rows goal)) {rr:List (Wire S)} {p bk L}
    (hp:Reach rr p bk) (hs:supply bk (ws.map (z3 rows)))
    (hl:∀ q bs,Reach rr q bs → z7 bs (z3 rows goal) → L ≤ q) :
    L + mass (ws.map (z3 rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩:=contraction nc (restrict_run rows h) rr hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def z6 (a:Sig):Wire Row:=fun r => bit r a
def table (f:Wire Row):Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f:Wire Row) (r:Row):bit r (table f) = f r:=by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v:Sig):table (z6 v) = v:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (z6 v) ⟨j,hj⟩
theorem observe_table (f:Wire Row):z6 (table f) = f:=by
  funext r
  exact bit_table f r
theorem obs_neg (a:Sig):z6 (neg a) = inv (z6 a):=by
  funext r
  exact bit_neg _ _
theorem obs_bin (d:Bool) (a b:Sig) :
    z6 (bin d a b) = combine d (z6 a) (z6 b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β:Type} (f:α → β) (d:Bool) (a:α) (l:List α) :
    (kept d a l).map f = kept d (f a) (l.map f):=by cases d <;> rfl
theorem kept_nd {α:Type} (k:Bool) (a:α) (l:List α)
    (hn:l.Nodup) (ha:a ∉ l):(kept k a l).Nodup:=by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k:Bool) (a:Sig) (l:List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [kept]
theorem list_run {T:Sig} {k u S} (h:Live T k u S) (v:List Sig)
    (hv:v.Nodup) (eqv:v.toFinset = S):Run (z6 T) k (v.map z6):=by
  classical
  induction h using Live.elimP generalizing v with
  | stop hp =>
    have eq:[T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=kept save a rest
    have er:rest.toFinset = U.erase a:=by simp [rest]
    have hm:a ∉ rest:=by simp [rest]
    have hr:rest.Nodup:=Finset.nodup_toList _
    have ht:tail.toFinset = U:=by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh:a ∈ U <;> simp [save,hh]
    have nd:=kept_nd save a rest hr hm
    have hf:neg a ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm:(a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=kept kb b rest
    let tail:=kept ka a mid
    have er:rest.toFinset = (U.erase a).erase b:=by simp [rest]
    have ar:a ∉ rest:=by simp [rest]
    have br:b ∉ rest:=by simp [rest]
    have hr:rest.Nodup:=Finset.nodup_toList _
    have bm:=kept_nd kb b rest hr br
    have am:a ∉ mid:=by cases h:kb <;> simp [mid,kept,h,hab,ar]
    have nd:=kept_nd ka a mid bm am
    have ht:tail.toFinset = U:=by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases aj:j=a <;>
        by_cases bj:j=b <;> simp_all [ka,kb]
    have hf:bin d a b ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map z6) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm:(a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja:j=a <;> by_cases jb:j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f:Wire Row):table (inv f) = neg (table f):=by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_bin (d:Bool) (f g:Wire Row) :
    table (combine d f g) = bin d (table f) (table g):=by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]
theorem available_rep {bk:List (Wire Row)} {a} (h:z7 bk a) :
    represented (bk.map table) (table a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z:table (fun _ => false) = zero:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z:table (fun _ => true) = one:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha:represented w a) :
    represented w (neg a) ∨ witness w (neg a):=by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem pull_cons {w:List Sig} {z:Sig} {T k t S} (h:Live T k t S)
    (hz:represented w z ∨ witness w z) (hs:∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem reach_live_sub {rr:List (Wire Row)} {p bk}
    (h:Reach rr p bk) {T k t S} (run:Live T k t S)
    (sub:∀ a ∈ S,a ∈ bk.map table) :
    ∃ l v U,l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U,a ∈ rr.map table:=by
  induction h using Reach.elimP generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bk a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bk a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem reach_live {rr:List Sig} {p bk T} (hp:proper T)
    (h:Reach (rr.map z6) p bk) (hit:z7 bk (z6 T)) :
    ∃ k t S,k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S,a ∈ rr:=by
  have hm:=available_rep hit
  rw [table_observe] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩:=reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem live_row_difference {T k t S} (h:Live T k t S) {r s:Row}
    (diff:bit r T ≠ bit s T):∃ a ∈ S,bit r a ≠ bit s a:=by
  induction h using Live.elimP with
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
    · by_cases aeq:bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {T k t S} (h:Live T k t S) (rr:List Sig) (a:Sig)
    (sub:∀ v ∈ S,v ∈ rr) (r s:Row) (diff:bit r T ≠ bit s T)
    (isolated:∀ v ∈ rr,v ≠ a → bit r v = bit s v):a ∈ S:=by
  obtain ⟨v,hv,hd⟩:=live_row_difference h diff
  by_cases veq:v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs:List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def grf:Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed:Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def sample (r:Row) (j:Fin 9):=bit r (inputs.getD j.val zero)
def edge (x:Fin 9 → Bool):Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table:∀ r:Row,bit r grf = edge (sample r):=by decide +kernel
theorem seed_table:∀ r:Row,bit r seed = (sample r 0 && sample r 1):=by decide +kernel
theorem graph_proper:proper grf:=by unfold proper; decide +kernel
theorem seed_nonzero:seed ≠ zero:=by decide +kernel
theorem input_list:List.ofFn (fun j:Fin 9 => inputs.getD j.val zero) = inputs:=rfl
theorem sampled (r:Row):List.ofFn (sample r) = inputs.map (bit r):=by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
def rename (f:Row → Row) (a:Sig):=table fun r => bit (f r) a
theorem bit_rename (f:Row → Row) (a:Sig) (r:Row) :
    bit r (rename f a) = bit (f r) a:=bit_table _ _
theorem observe_rename (f:Row → Row) (a:Sig) :
    z6 (rename f a) = z3 f (z6 a):=by funext r; exact bit_rename f a r
theorem rename_neg (f:Row → Row) (a:Sig):rename f (neg a) = neg (rename f a):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f:Row → Row) (d:Bool) (a b:Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f:Row → Row) (onto:Function.Surjective f) :
    Function.Injective (rename f):=by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f:Row → Row):rename f zero = zero ∧ rename f one = one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h:Live T k t S) (f:Row → Row) (onto:Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)):=by
  have inj:=rename_inj f onto
  obtain ⟨fz,fo⟩:=rename_constants f
  have pp (v) (p:proper v):proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.elimP with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh:rename f (neg a) ∉ (insert a U).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh:rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {T k t S} (h:Live T k t S) (none:t=0) {r s:Row}
    (pos:bit r T = true) (negRow:bit s T = false) :
    ∃ a ∈ S,bit r a = true ∧ bit s a = false:=by
  induction h using Live.elimP with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩:=ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p:bit r a <;> cases q:bit s a <;>
        cases u:bit r b <;> cases z:bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (rr:List Sig) (T:Sig) (L:Nat):Prop :=
  ∀ p bk,Reach (rr.map z6) p bk → z7 bk (z6 T) → L ≤ p
def Impossible (T:Sig) (cap:Nat) (S:Finset Sig):Prop :=
  ∀ k t,k ≤ cap → ¬Live T k t S
def Essential (T:Sig) (rr:List Sig) (a:Sig):Prop :=
  ∃ r s:Row,bit r T ≠ bit s T ∧ ∀ v ∈ rr,v ≠ a → bit r v = bit s v
theorem lower_impossible {rr T L} (hp:proper T)
    (essential:∀ a ∈ rr,Essential T rr a)
    (noRun:Impossible T L rr.toFinset):Lower rr T (L+1):=by
  intro p bk h ha
  obtain ⟨k,t,S,hk,run,hs⟩:=reach_live hp h ha
  have he:rr.toFinset = S:=by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:=essential _ hm
    exact raw_required run rr a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem observe_proper {v:Sig} (hv:proper v):¬Constant (z6 v):=by
  rintro ⟨b,h⟩
  have hr:represented ([]:List Sig) v:=by
    have avail:z7 ([]:List (Wire Row)) (z6 v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv
theorem mass_append {R} (a b:List (Wire R)):mass (a++b) = mass a + mass b:=by
  simp [mass]
theorem mass_constants {R} (xs:List (Wire R)) (hc:∀ x ∈ xs,Constant x) :
    mass xs = xs.length:=by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {rr other:List Sig} {T G:Sig} (pT:proper T) (pG:proper G)
    (r:Row → Row) (eq:rename r T = G)
    (covered:∀ a ∈ rr,z7 (other.map z6) (z6 (rename r a)))
    (singles:Finset Sig) (necessary:∀ a ∈ singles,Essential T rr a)
    (constant:∀ a ∈ singles,Constant (z6 (rename r a)))
    (L:Nat) (prior:Lower other G L):Lower rr T (L + singles.card):=by
  classical
  intro p bk hh ha
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live pT hh ha
  have subS:singles ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:=necessary a hs
    exact raw_required run rr a sub i j hd hiso
  let front:=singles.toList ++ (S \ singles).toList
  have nd:front.Nodup:=by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe:front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':=list_run run front nd fe
  have gc:z3 r (z6 T) = z6 G:=(observe_rename _ _).symm.trans (congrArg z6 eq)
  have supp:supply (other.map z6) ((front.map z6).map (z3 r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo:singles.card ≤ mass ((front.map z6).map (z3 r)):=by
    simp only [front,List.map_append,mass_append]
    let xs:=(singles.toList.map z6).map (z3 r)
    have only:∀ v ∈ xs,Constant v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def childOne (ws:List Sig) (a:Sig) (keep:Bool):List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws:List Sig) (a b:Sig) (d ka kb:Bool):List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l:List Sig} (h:l.Nodup) (a:Sig):(l.erase a).toFinset = l.toFinset.erase a:=by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T:Sig} {cap:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
    (oneStep:∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep:∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset:=by
  classical
  intro k t hk h
  generalize he:ws.toFinset = S at h
  induction h using Live.elimP with
  | stop hp =>
    have mem:T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am:a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh:neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest:(kept keep a (ws.erase a)).toFinset = U:=by
      rw [kept_fin,er,he]
      by_cases hm:a ∈ U <;> simp [keep,hm]
    have nd:(childOne ws a keep).Nodup:=by
      have na:a ∉ ws.erase a:=hn.not_mem_erase
      have nk:=kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq:(childOne ws a keep).toFinset = insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len:(childOne ws a keep).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am:a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm:b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh:bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er:rest.toFinset = (ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke:(kept ka a (kept kb b rest)).toFinset = U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases ja:j=a <;>
        by_cases jb:j=b <;> simp_all [ka,kb]
    have rn:rest.Nodup:=(hn.erase _).erase _
    have ar:a ∉ rest:=fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br:b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax:a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd:(childTwo ws a b d ka kb).Nodup:=by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq:(childTwo ws a b d ka kb).toFinset = insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc:=(live_size tail).2
    have len:(childTwo ws a b d ka kb).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T:Sig) (width:Nat) (pos negRow:Fin width → Row)
    (asig:Sig → BitVec width × BitVec width):Prop :=
  (∀ i,bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i,(asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented:Bool) (s:BitVec n × BitVec n):BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented:Bool) (sig:Sig → BitVec n × BitVec n):List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n:Nat} {oriented:Bool} {sig:Sig → BitVec n × BitVec n} {ws:List Sig} {i:Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val = true:=by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {T k t S} (h:Live T k t S) {ws:List Sig} (he:ws.toFinset=S)
    {width:Nat} {r s:Fin width → Row} {sig} (correct:Sep T width r s sig)
    (oriented:Bool) (zeroNot:oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i:Fin width:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩:=live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx:bit (r i) a <;> cases hy:bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩:=mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {T cap ws k t} (h:Live T k t (List.toFinset ws))
    (hk:k ≤ cap) (hn:ws.Nodup) {n:Nat} {r s:Fin n → Row} {sig}
    (correct:Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n:=by
  apply cover_sound h rfl correct
  intro hh
  have eq:=of_decide_eq_true hh
  have bound:=(live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw:List Sig) (T d:Sig) (L:Nat):Prop :=
  ∃ (f:Row → Row) (rr:List Sig),(∀ r,bit (f r) d = true) ∧
    (∀ a ∈ raw,z7 (rr.map z6) (z3 f (z6 a))) ∧
    ¬Constant (z3 f (z6 T)) ∧
    ∀ p bk,Reach (rr.map z6) p bk → z7 bk (z3 f (z6 T)) → L ≤ p
def masked (d a:Sig):=a &&& d
def availableB (d:Sig) (pool:List Sig) (a:Sig) :=
  let m:=masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)
theorem masked_eq {f:Row → Row} {d a b:Sig} (dom:∀ r,bit (f r) d = true)
    (eq:masked d a = masked d b) :
    z3 f (z6 a) = z3 f (z6 b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem masked_zero {f:Row → Row} {d a:Sig} (dom:∀ r,bit (f r) d = true)
    (eq:masked d a = zero):z3 f (z6 a) = fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem masked_one {f:Row → Row} {d a:Sig} (dom:∀ r,bit (f r) d = true)
    (eq:masked d a = d):z3 f (z6 a) = fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def poolSupply (f:Row → Row) (bk:List (Wire Row)) (pool:List Sig) :=
  ∀ a ∈ pool,z7 bk (z3 f (z6 a))
theorem availableB_sound {f:Row → Row} {d a:Sig} {bk pool}
    (dom:∀ r,bit (f r) d = true) (supplyB:poolSupply f bk pool)
    (check:availableB d pool a = true):z7 bk (z3 f (z6 a)):=by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice:=Nat × Sig × Sig
def cvv (c:Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d:Sig) (pool:List Sig) (c:Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)
theorem pay_choice {f:Row → Row} {d:Sig} {rr bk pool q}
    (dom:∀ r,bit (f r) d = true) (hp:Reach rr q bk) (hs:poolSupply f bk pool)
    (c:Choice) (valid:choiceOK d pool c = true) :
    ∃ next,Reach rr (q+1) next ∧ poolSupply f next (cvv c :: pool):=by
  have ok:availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true:=by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha:=availableB_sound dom hs ok.1
  let z:=z3 f (z6 (cvv c))
  have hz:Reach rr (q+1) (z::bk):=by
    by_cases unary:c.1=2
    · change Reach _ _ (z3 f (z6 (cvv c)) :: _)
      rw [cvv,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb:availableB d pool c.2.2 = true:=by simpa [unary] using ok.2
      have hz':=Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (z3 f (z6 (cvv c)) :: _)
      rw [cvv,if_neg unary,obs_bin]
      have comm (b:Bool) (v w:Wire Row):z3 f (combine b v w) = combine b (z3 f v) (z3 f w):=by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)
def makePool (d:Sig) (pool:List Sig):List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (cvv c::pool) cs else none
theorem makePool_sound {d:Sig} {f:Row → Row} (dom:∀ r,bit (f r) d = true)
    {rr bk q pool} (hp:Reach rr q bk) (hs:poolSupply f bk pool)
    (cs:List Choice) {result} (ok:makePool d pool cs = some result) :
    ∃ next,Reach rr (q+cs.length) next ∧ poolSupply f next result:=by
  induction cs generalizing bk q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩:=pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩:=ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def z9 (d a:Sig):=masked d a == zero || masked d a == d
theorem count_constants {d:Sig} {f:Row → Row} (dom:∀ r,bit (f r) d = true)
    (ws:List Sig):ws.countP (z9 d) ≤ mass ((ws.map z6).map (z3 f)):=by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h:z9 d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc:Constant (z3 f (z6 a)):=by
        have hh:masked d a = zero ∨ masked d a = d:=by simpa only [z9,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d:Sig) (L k p:Nat) (pool ws:List Sig) :=
  decide (k+p < L+ws.countP (z9 d)) && ws.all (availableB d pool)
theorem poolCut_sound {raw T d L} (slice:Slice raw T d L) (cs:List Choice)
    {pool ws cap} (built:makePool d raw cs = some pool)
    (nd:ws.Nodup) (cut:poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,rr,dom,base,nc,lo⟩:=slice
  obtain ⟨bk,hr,hs⟩:=makePool_sound dom (Reach.start (rr:=rr.map z6)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:=cut
  have coveredS:supply bk ((ws.map z6).map (z3 f)):=by
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
def shifted (d r:Row):Row :=
  if h:r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d:Row):Row:=Fin.ofNat 512 (512-d.val)
def rowMove (m:Move) (r:Row):Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b:Sig):=(m &&& a) ||| (~~~m &&& b)
def wordMove (m:Move) (a:Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r:Row) (a:Sig):bit r (a.rotateRight d.val) = bit (shifted d r) a:=by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h:r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y:Bool):(p && x || !p && y) = (if p then x else y):=by cases p <;> simp
theorem bit_mux (r:Row) (m a b:Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r:Row) (m:Move) (a:Sig):bit r (wordMove m a) = bit (rowMove m r) a:=by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms:List Move) (r:Row):=ms.foldl (fun j m => rowMove m j) r
def movedWord (ms:List Move) (a:Sig):=ms.foldr wordMove a
theorem bit_moved (ms:List Move) (a:Sig) (r:Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms:List Move) (a:Sig):movedWord ms a = rename (movedRow ms) a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm
def freeWord (rr:List Sig) (w:Sig):=w==zero || w==one || rr.contains w
theorem freeWord_ok {rr w} (ok:freeWord rr w = true) :
    z7 (rr.map z6) (z6 w):=by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms:List Move) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {ms raw T base G} (ok:checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw,z7 (base.map z6) (z6 (rename (movedRow ms) a)):=by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok:checkMap ms raw T base G = true)
    (pT:proper T) (pG:proper G) (hL:Lower base G L):Lower raw T L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {ms raw T base G L d} (ok:checkMap ms raw T base G = true)
    (all:movedWord ms d = one) (properG:proper G) (hL:Lower base G L) :
    Slice raw T d L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  have obs:z3 (movedRow ms) (z6 T) = z6 G :=
    (observe_rename _ _).symm.trans (congrArg z6 eq)
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
def witnessB (T:Sig) (rr:List Sig) (a:Sig) (rs:Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  rr.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T rr a rs} (ok:witnessB T rr a rs = true):Essential T rr a:=by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok:checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)
theorem lower_count {raw T} (properT:proper T) (xs:List (Sig × Row × Row))
    (ok:checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p bk hr hit
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live properT hr hit
  have le:(xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:=essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound:=(live_size run).2
  omega
def checkLift (ms:List Move) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
    (xs:List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)
theorem lift_ok {ms T raw base G xs L} (ok:checkLift ms T raw base G xs = true)
    (properT:proper T) (properG:proper G) (low:Lower base G L) :
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
def selected (m:Nat):List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m:Nat):=(selected m).map Prod.snd
def vertex (m j:Nat):=if m.testBit j then inputs.getD j zero else zero
def z5 (m:Nat):Sig :=
  let x:=vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0:Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3:Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6:Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o:Nat):Sig :=
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o:Nat):List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v:Nat):Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask:Nat):List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints:Nat):List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def prB (T:Sig):=T != zero && T != one
theorem proper_of (T:Sig) (h:prB T = true):proper T:=by
  simpa only [prB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L:Nat) :=
  let xs:=graphPairs m hints
  prB (z5 m) && checkEssential (z5 m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h:assertSize m hints L = true) :
    Lower (vars m) (z5 m) L:=by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bk hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bk hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o:Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m:Nat):Sig :=
  if m=1023 then z5 m &&& ~~~seed else z5 m
def colCheck (m:Nat) (c:ColumnInfo) (prior:Nat → Nat):Bool :=
  let (z,o,q,s,L):=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  let count:=(xs.map Prod.fst).toFinset.card
  prB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else prB (z5 q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (z5 q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {m:Nat} (c:ColumnInfo) (prior:Nat → Nat)
    (valid:∀ q,Lower (vars q) (z5 q) (prior q))
    (ok:colCheck m c prior = true):Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩:=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  change (((prB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bk hr ha
  have hh:=ok.2
  by_cases hq:q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bk hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bk hr ha)
def relabelOK (old rep:Nat) (swaps:List Nat) :=
  prB (z5 old) && prB (z5 rep) &&
    checkMap (swaps.map swapRows) (vars old) (z5 old) (vars rep) (z5 rep)
theorem relabel_of {old rep L swaps} (ok:relabelOK old rep swaps = true)
    (h:Lower (vars rep) (z5 rep) L):Lower (vars old) (z5 old) L:=by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
def bsB (entries:List (Nat × Nat)) (q:Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries:List (Nat × Nat))
    (sound:∀ e ∈ entries,Lower (vars e.1) (z5 e.1) e.2) (q:Nat) :
    Lower (vars q) (z5 q) (bsB entries q):=by
  unfold bsB
  cases h:entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit:(fun a:Nat × Nat => a.1 == q) e = true:=List.find?_some (p:=fun a:Nat × Nat => a.1 == q) (a:=e) h
    have eq:e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.dmn (v:BoundPool):Sig:=v.1
abbrev BoundPool.bound (v:BoundPool):Nat:=v.2.1
abbrev BoundPool.paid (v:BoundPool):Nat:=v.2.2.1
abbrev BoundPool.wires (v:BoundPool):List Sig:=v.2.2.2
def ValidPool (raw:List Sig) (T:Sig) (c:BoundPool) :=
  ∃ (f:Row → Row) (rr:List Sig) (bk:List (Wire Row)),
    (∀ r,bit (f r) c.dmn = true) ∧ ¬Constant (z3 f (z6 T)) ∧
    (∀ q ws,Reach (rr.map z6) q ws → z7 ws (z3 f (z6 T)) → c.bound ≤ q) ∧
    Reach (rr.map z6) c.paid bk ∧ poolSupply f bk c.wires ∧ True
theorem build_valid {raw T d lb} (h:Slice raw T d lb) (cs:List Choice) {ws}
    (build:makePool d raw cs = some ws):ValidPool raw T ⟨d,lb,cs.length,ws⟩:=by
  obtain ⟨f,rr,dom,sup,nc,prior⟩:=h
  obtain ⟨bk,hr,hs⟩:=makePool_sound dom (Reach.start (rr:=rr.map z6)) sup cs build
  exact ⟨f,rr,bk,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem valid_exclude {raw T c} (valid:ValidPool raw T c) (k:Nat) (rest:List Sig)
    (choice:Choice) (paid:Bool)
    (known:∀ a ∈ rest,availableB c.dmn c.wires a = true)
    (buy:if paid then choiceOK c.dmn c.wires choice = true
       else availableB c.dmn c.wires (cvv choice) = true)
    (bound:k+c.paid+paid.toNat <
      c.bound+(cvv choice :: rest).countP (z9 c.dmn))
    (nd:(cvv choice :: rest).Nodup) :
    Impossible T k (cvv choice :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,rr,bk,dom,nc,lo,hp,hs,_⟩:=valid
  let ws:=cvv choice::rest
  have done (n:Nat) (out:List (Wire Row)) (reach:Reach (rr.map z6) n out)
      (zs:poolSupply f out (cvv choice::rest)) (le:n = c.paid+paid.toNat):False:=by
    have covered:supply out ((ws.map z6).map (z3 f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
      exact zs _ ha
    have b:=projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm:=count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (z9 c.dmn) at bound
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
      · have ha:availableB c.dmn c.wires a = true:=known _ hm
        have point:∀ u ∈ c.wires,z7 out (z3 f (z6 u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con
def scalarPoolCut (c:BoundPool) (k:Nat) (rest:List Sig) (op:Choice) :=
  let z:=cvv op
  let exa:=!(availableB c.dmn c.wires z)
  ((k+c.paid+exa.toNat < c.bound+(z::rest).countP (z9 c.dmn)) &&
    rest.all (availableB c.dmn c.wires)) && (!exa || choiceOK c.dmn c.wires op)
theorem scalarPoolCut_sound {raw T c} (valid:ValidPool raw T c) {k rest op}
    (nd:(cvv op::rest).Nodup) (cut:scalarPoolCut c k rest op = true) :
    Impossible T k (cvv op::rest).toFinset:=by
  let exa:=!(availableB c.dmn c.wires (cvv op))
  apply valid_exclude valid k rest op exa _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he:availableB c.dmn c.wires (cvv op) <;> simp_all [exa]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw:List Sig) (cs:List Choice) (d:Sig) (lb:Nat):Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice:Slice raw T d L)
    (h:materialize raw cs d L = some c):ValidPool raw T c:=by
  unfold materialize at h
  cases he:makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n:Nat} (r:Fin n → Row) (v:Sig):BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n:Nat} (r:Fin n → Row) (v:Sig) (i:Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v:=by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s:Fin 768 → Row) (a:Sig):Signals:=(ofRows r a,ofRows s a)
def properPairs (T:Sig) (r s:Fin 768 → Row) :=
  ∀ i,bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h:properPairs T r s):Sep T 768 r s (pairSig r s):=by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s:Fin 768 → Row) (x:Decor):=x.2 = pairSig r s x.1
def dneg (x:Decor):Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d:Bool) (x y:Decor):Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r:Fin 768 → Row) (a:Sig):ofRows r (neg a) = ~~~ofRows r a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r:Fin 768 → Row) (d:Bool) (a b:Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h:faithful r s x):faithful r s (dneg x):=by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg,h]
theorem faithful_bin {r s x y} (d) (hx:faithful r s x) (hy:faithful r s y) :
    faithful r s (dbin d x y):=by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op:Nat) (x y:Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor:Decor:=(zero,0,0)
theorem faithful_default (r s):faithful r s defaultDecor:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0:Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0:Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all:∀ v ∈ ws,faithful r s v) (i:Nat) :
    faithful r s (List.getD ws i defaultDecor):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e:ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n:Nat) (bits:Nat) (ws:List Decor):List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base:∀ v ∈ ws,faithful r s v) :
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
def asRow (cols:Nat → Bits) (i:Fin 768):Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0:∀ r:Row,bit r (inputs.getD 0 zero) = r.val.testBit 0:=by decide +kernel
theorem coordinate1:∀ r:Row,bit r (inputs.getD 1 zero) = r.val.testBit 1:=by decide +kernel
theorem coordinate2:∀ r:Row,bit r (inputs.getD 2 zero) = r.val.testBit 2:=by decide +kernel
theorem coordinate3:∀ r:Row,bit r (inputs.getD 3 zero) = r.val.testBit 3:=by decide +kernel
theorem coordinate4:∀ r:Row,bit r (inputs.getD 4 zero) = r.val.testBit 4:=by decide +kernel
theorem coordinate5:∀ r:Row,bit r (inputs.getD 5 zero) = r.val.testBit 5:=by decide +kernel
theorem coordinate6:∀ r:Row,bit r (inputs.getD 6 zero) = r.val.testBit 6:=by decide +kernel
theorem coordinate7:∀ r:Row,bit r (inputs.getD 7 zero) = r.val.testBit 7:=by decide +kernel
theorem coordinate8:∀ r:Row,bit r (inputs.getD 8 zero) = r.val.testBit 8:=by decide +kernel
theorem input_coords:∀ (j:Fin 9) (r:Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val:=by
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
theorem asRow_bit (cols:Nat → Bits) (i:Fin 768) (j:Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val:=by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m:Nat) (p q:Nat → Bits):List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h:(j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q:Nat → Bits) :
    ∀ a ∈ rawDecor m p q,faithful (asRow p) (asRow q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:=selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m:Nat) (v:Nat → Bits):Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m:Nat) (v:Nat → Bits) (i:Fin 768) (j:Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0):Bits).getLsbD i.val:=by
  by_cases hh:m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m:Nat) (v:Nat → Bits) (i:Fin 768) :
    bit (asRow v i) (z5 m) = (liftGoal m v).getLsbD i.val:=by
  have pos (j:Nat) (hj:j<9):(vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0):Bits).getLsbD i.val:=bit_vertex m v i ⟨j,hj⟩
  simp only [bit,z5,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=Bits × Bits × Bits
def addCov (z:Bits) (c:Cov):Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d:Bool) (v:List Decor):Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c:Cov) (a:Bits):Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c:Cov) (a b:Bits):Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
theorem cov_one (c:Cov) (a:Bits):takeOne (addCov a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
theorem cov_two (c:Cov) (a b:Bits):takeTwo (addCov a (addCov b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem add_swap (c:Cov) (a b:Bits):addCov a (addCov b c)=addCov b (addCov a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
theorem cov_perm (d:Bool) {l r:List Decor} (h:l.Perm r):coverage d l=coverage d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d:Bool) (v:List Decor) {r s} (good:∀ a ∈ v,faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws:List Decor) (a:Decor) (keep:Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws:List Decor) (a b:Decor) (ka kb:Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws:List Decor} (a:Decor) (ha:a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
theorem cover_one {ws:List Decor} (d:Bool) (a:Decor) (ha:a ∈ ws) (keep:Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)):=by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws:List Decor} (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws:List Decor} (d:Bool) (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (ka kb:Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)):=by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b:List Sig):=(a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h:sameWords xs ys = true):xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v:Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs:List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools:List BoundPool) (links:Nat → List (List Sig)) (k:Nat)
    (rest:List Sig) (op:Choice) :=
  let ws:=cvv op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChild_sound {raw T pools links k rest op}
    (pValid:∀ p ∈ pools,ValidPool raw T p)
    (lValid:∀ tag xs,xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd:(cvv op :: rest).Nodup)
    (h:closeChild pools links k rest op = true) :
    Impossible T k (cvv op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair:=Cov × Cov
def preCov (ws:List Decor):CovPair:=(coverage false ws,coverage true ws)
def getCov (c:CovPair) (d:Bool):=if d then c.2 else c.1
theorem get_preCov (ws) (d:Bool):getCov (preCov ws) d = coverage d ws:=by cases d <;> rfl
def restCov (v:Cov) (a b:Bits) (un ka kb:Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb:Bool) (a b:Decor) (ws:List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
theorem rest_coverage {ws:List Decor} {a b:Decor} (ha:a ∈ ws) (hb:b ∈ ws)
    (un ka kb d:Bool) (ne:un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb:=by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka
theorem delOne_sub (ws:List Decor) (a:Decor) (k:Bool):(delOne ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws:List Decor) (a b:Decor) (un ka kb:Bool) :
    (opKeep un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws:List Decor) (a b:Decor) (un ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1):=by
  cases un
  · have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op:Nat) (a b:Decor):=codeDecor op a b
def movedChoice (op:Nat) (a b:Decor):Choice:=(op,a.1,b.1)
theorem moved_full (op) (a b:Decor) :
    (movedDecor op a b).1 = cvv (movedChoice op a b):=by
  by_cases h:op=2
  · simp [movedDecor,codeDecor,h,dneg,cvv,movedChoice]
  · cases hh:op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,cvv,movedChoice]
theorem moved_faithful {r s a b} (ha:faithful r s a) (hb:faithful r s b) (op:Nat) :
    faithful r s (movedDecor op a b):=by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c:NodeContext) (op:Nat) (a b z:Decor) (ka kb:Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d:=len==cap
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !prB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws:List Decor) (op:Nat) (a b:Decor) (ka kb:Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs:properPairs T r s) (faith:∀ w ∈ ws,faithful r s w)
    (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:(op==2)=false → a≠b) (hcap:0<cap)
    (pv:∀ p ∈ pools,ValidPool raw T p)
    (lv:∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro:proper (movedDecor op a b).1) (fresh:(movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test:evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub:rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc:child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr:ws.any (fun v => v.1==z.1) = false:=by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp:prB z.1 = true:=by simpa [prB,proper] using pro
  have leq:1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length:=by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz:=(live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len:child.length ≤ cap:=by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep:=cover_required h hk ndc (pair_sep pairs)
  have ce:cap-1+1=cap:=by omega
  rw [ce] at sep
  let d:=child.length==cap
  have g:(coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  have deq:decide (child.length=cap) = (child.length==cap):=by by_cases he:child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be:((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false:=by simp [sep]
  change (if (_ != _) then true else if !prB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val:=moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd':=ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h
def testPair (ctx:NodeContext) (a b:Decor) (d:Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx:NodeContext) (a:Decor) (bs:List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx:NodeContext):List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs
theorem all_unary {ctx ws} (h:testAll ctx ws=true) {a:Decor} (ha:a∈ws) (keep:Bool) :
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
theorem all_binary {ctx ws} (h:testAll ctx ws=true) {a b:Decor} (ha:a∈ws) (hb:b∈ws)
    (ne:a≠b) (d:Bool):testPair ctx a b d=true ∨ testPair ctx b a d=true:=by
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
theorem testPair_at {ctx a b d} (h:testPair ctx a b d = true) (ka kb:Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true:=by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v:List Sig} {w:Sig} (a:Sig) (k:Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v:=by cases k <;> simp [kept]
theorem mem_delone {v:List Decor} (nd:v.Nodup) (a w:Decor) (k:Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true):=by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
    (ha:a∈ws) (hb:b∈ws) (eq:a.1=b.1):a=b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem kept_value {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
    (ha:a ∈ ws) (hb:b ∈ ws) (un ka kb:Bool) (v:Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true):=by
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
theorem unary_front {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a:Decor} (ha:a∈ws)
    (keep:Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e:v=a.1 <;> cases keep <;> simp_all
theorem binary_front {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
    (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d ka kb:Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va:v=a.1 <;> by_cases vb:v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v:List Sig) (nd:v.Nodup) (a b:Sig) (d ka kb:Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset:=by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs:properPairs T r s) (faith:∀ w ∈ ws,faithful r s w)
    (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
    (pv:∀ p ∈ pools,ValidPool raw T p)
    (lv:∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks:testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset:=by
  by_cases hc:cap=0
  · intro k t hk h
    have ke:k=0:=by omega
    subst k
    generalize he:(ws.map Prod.fst).toFinset = S at h
    have onlyTarget:∀ {k t T S},Live T k t S → k=0 → S={T}:=by
      intro k t T S hh
      induction hh using Live.elimP <;> simp
    rw [onlyTarget h rfl] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc':0<cap:=by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab:a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b:Decor) (aa:a∈ws) (bb:b∈ws) (ne':a.1≠b.1) (ka kb:Bool)
        (pr:proper (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test:testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      rw [←binary_front nd aa bb ne']
      have eq:(movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1:=by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh
theorem agree_inputs (r s:Row) (h:∀ a ∈ inputs,bit r a = bit s a):r=s:=by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj:j<9
  · let i:Fin 9:=⟨j,hj⟩
    have hm:inputs.getD i.val zero ∈ inputs:=by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le:512 ≤ 2^j:=by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q:List Move):=inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h:composedOK p q = true) (r:Row) :
    movedRow q (movedRow p r) = r:=by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T:Sig) (p:List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws:List Sig} (hi:Impossible T n ws.toFinset)
    (p:List Move) (ok:autoOK T p = true):Impossible T n (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto:Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run:=live_rename h (movedRow p) onto
  have goal:rename (movedRow p) T = T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x:Sig):rename (movedRow p) (movedWord p.reverse x) = x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back:(ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset:=by
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
def emptyPacking:Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word:Nat → Nat) (pos len:Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw:Nat) (data:Nat → Nat) (h:Nat):Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev z1 (α:Type):=List α
def z1.leaf {α:Type} (xs:List α):z1 α:=xs
def z1.fork {α:Type} (_:Nat) (xs ys:z1 α):z1 α:=xs ++ ys
def z1.read {α:Type} (xs:z1 α) (i:Nat):=xs[i]?
def z1.values {α:Type} (xs:z1 α):=xs
theorem z1.read_mem {α} (tree:z1 α) {i x} (e:tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
abbrev Forest:=(Nat) × (Nat) × (Nat → Bits × Bits) × (z1 ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
abbrev Forest.mask (v:Forest):Nat:=v.1
abbrev Forest.cap (v:Forest):Nat:=v.2.1
abbrev Forest.samples (v:Forest):Nat → Bits × Bits:=v.2.2.1
abbrev Forest.cols (v:Forest):z1 ColumnInfo:=v.2.2.2.1
abbrev Forest.autos (v:Forest):Array (List Nat):=v.2.2.2.2.1
abbrev Forest.levels (v:Forest):Nat → Packing:=v.2.2.2.2.2.1
abbrev Forest.index (v:Forest):Nat → Nat → Option (Nat × Nat):=v.2.2.2.2.2.2
def wiresOf (g:Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g:Forest):∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:=by
  have base:=raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha
def targetOf (g:Forest):=chartGoal g.mask
def cSmp (m:Nat) (v:Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m:Nat) (v:Nat → Bits) (i:Fin 768) :
    bit (asRow v i) (chartGoal m) = (cSmp m v).getLsbD i.val:=by
  by_cases e:m=1023
  · have u:=asRow_bit v i (0:Fin 9)
    have w:=asRow_bit v i (1:Fin 9)
    have h:=bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq:seed = inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
    simp only [chartGoal,cSmp,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,cSmp,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m:Nat} {p q:Nat → Bits}
    (hp:cSmp m p = BitVec.allOnes 768) (hq:cSmp m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q):=by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α:Type} (bits:Nat):List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α:Type} (bits:Nat) (ws:List α):(selectLive bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def storedLen (g:Forest) (depth:Nat):=if g.cap=13 ∧ g.mask=511 then 10*depth-16 else 10*depth
def readNode (g:Forest) (k i:Nat):Nat × List Decor × List Decor :=
  let raw:=wiresOf g
  let (_,depth,_,_,_,_,_,data):=g.levels k
  let len:=storedLen g depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i*width) width
  let stored:=recp &&& ((1 <<< len)-1)
  let ops:=if g.cap=13 ∧ g.mask=511 then 512 + ((256+16*(stored % 16)) <<< 10) + ((stored >>> 4) <<< 20) else stored
  let bk:=decodeBank depth ops raw
  (ops,bk,selectLive (recp >>> len) bk)
def getFieldV (x pos width:Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bk:List Decor) (ops paid:Nat):Nat → List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bk (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bk.getD (ops &&& 15) defaultDecor).1,
        (bk.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g:Forest) (ops d:Nat) (bk:List Decor) (idx paid:Nat):Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bk ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g:Forest)
    (cols:∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bk paid c} (h:buildRule g ops depth bk i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c:=by
  unfold buildRule at h
  cases e:g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data:Nat → Nat) (w v:Nat):Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g:Forest) (k i:Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g:Forest) (k:Nat) (pair:Nat × Nat):Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g:Forest) (k:Nat)
    (names:∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows) = true)
    (earlier:∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h:linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset:=by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e:g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def nodeVerified (g:Forest) (k i:Nat) :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bk,ws):=readNode g k i
  let values:=ws.map Prod.fst
  let start:=num*(storedLen g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bk a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
theorem nodeVerified_sound (g:Forest) (k i:Nat)
    (samples:properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols:∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names:∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows) = true)
    (prior:k>0 → ∀ j < (g.levels (k-1)).1,Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked:nodeVerified g k i = true):Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN:=checked.1.1
  have hT:targetOf g ∉ stateSet g k i:=by simpa [stateSet] using checked.1.2
  by_cases h0:k=0
  · subst k
    intro t u lo h
    have ht:t=0:=by omega
    subst t
    generalize he:(stateSet g 0 i).toFinset = S at h
    have onlyTarget:∀ {k t T S},Live T k t S → k=0 → S={T}:=by
      intro k t T S hh
      induction hh using Live.elimP <;> simp
    rw [onlyTarget h rfl] at he
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e:((g.index k tag).bind (linkedSet g (k-1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g:Forest) (k start:Nat):Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h:block g k start n=true) (j:Nat) (lo:start≤j) (hi:j<start+n) :
    nodeVerified g k j=true:=by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq:j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem z2 {g k start a b} (h:block g k start a=true)
    (h':block g k (start+a) b=true):block g k start (a+b)=true:=by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g:Forest) (top:Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1 = true
def graphValid (g:Forest) (prior:Nat → Nat) :=
  (cSmp g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (cSmp g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g:Forest) (top:Nat) (prior:Nat → Nat)
    (lower:∀ q,Lower (vars q) (z5 q) (prior q))
    (geometry:graphValid g prior = true) (rows:checkedTables g top) :
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
def indexedRoot (g:Forest) (k i:Nat) (ws:List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low:∀ q,Lower (vars q) (z5 q) (prior q))
    (geom:graphValid g prior = true) (blocks:checkedTables g top) (le:k ≤ top)
    (idx:indexedRoot g k i ws = true):Impossible (targetOf g) k ws.toFinset:=by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low:∀ q,Lower (vars q) (z5 q) (prior q))
    (geom:graphValid g prior = true) (blocks:checkedTables g g.cap)
    (idx:indexedRoot g g.cap i (vars g.mask) = true) (hp:prB (targetOf g) = true)
    (ess:checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all:(graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem lower_discard {g prior ci hints} (low:∀ q,Lower (vars q) (z5 q) (prior q))
    (ok:colCheck g.mask ci prior = true)
    (hp:prB (targetOf g) = true)
    (ess:checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all:(graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd:(vars g.mask).Nodup)
    (cut:poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries:List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (z5 e.1) e.2
def extendKnown (old:List (Nat × Nat)) (L:Nat) (relabels:List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous:Known old)
    (main:Lower (vars m) (z5 m) L)
    (ok:relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown:Known []:=by simp [Known]
def lanePlace (v:Nat) (upper:Nat):=2^769*upper+v
def z4 {α:Type} (f:α → Bits):List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (z4 f xs)
def units:Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x:Bits):x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b:Bits) (u v:Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h:i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b:Bits) (u v:Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h:i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b:Bits) (u v:Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h:i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g:α → Bits) (xs) :
    z4 f xs &&& z4 g xs = z4 (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [z4]
  | cons a xs ih => simp only [z4,place_and,ih]
theorem lanes_or {α} (f g:α → Bits) (xs) :
    z4 f xs ||| z4 g xs = z4 (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [z4]
  | cons a xs ih => simp only [z4,place_or,ih]
theorem lanes_xor {α} (f g:α → Bits) (xs) :
    z4 f xs ^^^ z4 g xs = z4 (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [z4]
  | cons a xs ih => simp only [z4,place_xor,ih]
theorem broadcast {α} (a:Bits) (xs:List α) :
    units xs.length * a.toNat = z4 (fun _ => a) xs:=by
  induction xs with
  | nil => simp [units,z4]
  | cons v xs ih => simp only [List.length_cons,units,z4,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed:Nat):=((packed+r) >>> 768) &&& r
theorem unit_bit (n i:Nat) (hi:i<n):(units n).testBit (769*i) = true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel:1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di:769*(i+1)-769=769*i:=by omega
      have ge:¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a:Bits):(a.toNat+1).testBit 768 = (a==BitVec.allOnes 768):=by
  by_cases h:a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne:a.toNat ≠ 2^768-1:=by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt:a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f:α → Bits) (xs:List α) (i:Nat) (hi:i<xs.length) :
    (fullMarks (units xs.length) (z4 f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [z4,List.length_cons,units,lanePlace]
    have sum (u v x:Nat):2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
    have hi':i < xs.length+1:=hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge:¬769*(i+1)+768<769:=by omega
      have di:769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig:=Nat × Nat
abbrev PackedCov:=Nat × Nat × Nat
def packedSig {α} (s:α → Signals) (xs:List α):PackedSig :=
  (z4 (fun x => (s x).1) xs,z4 (fun x => (s x).2) xs)
def packedCov {α} (c:α → Cov) (xs:List α):PackedCov :=
  (z4 (fun x => (c x).1) xs,z4 (fun x => (c x).2.1) xs,
   z4 (fun x => (c x).2.2) xs)
def packedColumn (d:Bool) (a:PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b:Bits):a ^^^ (a &&& b) = a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s:α → Signals) (xs:List α) (d:Bool) :
    packedColumn d (packedSig s xs) = z4 (fun x => column d (s x)) xs:=by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (full:Nat) (op:Nat) (a b:PackedSig):PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a:Bits):BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
theorem packed_op {α} (a b:α → Decor) (xs:List α) (op:Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs:=by
  by_cases un:op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one:op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]
def takePacked (c:PackedCov) (a b:Nat) (un ka kb:Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c:α → Cov) (a b:α → Bits) (xs:List α) (un ka kb:Bool) :
    takePacked (packedCov c xs) (z4 a xs) (z4 b xs) un ka kb =
    z4 (fun x => restCov (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def z8 (c:NodeContext) (i:Nat):=c.2.2.1.getD i defaultDecor
def checkAt (c:NodeContext) (i j op:Nat) (ka kb:Bool) :=
  let a:=z8 c i
  let b:=z8 c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c:NodeContext) (d un ka kb:Bool) (op i j:Nat) :=
  let a:=z8 c i
  let b:=z8 c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α:Type} (f:α → Bool) (mask:Nat):List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f:α → Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length)
    (bitOn:mask.testBit (769*i)=true) (ok:onMarks f mask xs=true):f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne:mask≠0:=by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero:mask &&& 1 ≠ 0:=by
        intro he
        have at0:=congrArg (fun n:Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:=Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n:Nat) (xs:List NodeContext):Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (z8 c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b:Batch) (i:Nat):=b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i:Nat} (h:i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (z8 c i).2) xs:=by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p:BoundPool) (m:Sig) :=
  m==zero || m==p.dmn || (p.wires.map (masked p.dmn)).any (fun v => v==m)
theorem available_mask (p:BoundPool) (x:Sig) :
    availableB p.dmn p.wires x = availableMasked p (masked p.dmn x):=rfl
def constantLoss (p:Decor → Bool) (a:Decor) (keep:Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p:Decor → Bool) (ws:List Decor) (a:Decor) (keep:Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep:=by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p:Decor → Bool) (ws:List Decor) (a b:Decor) (un ka kb:Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p:=by
  have h1:=lossBound p ws a ka
  have h2:=lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool:=BoundPool × Nat × Bool
def summarizePool (ws:List Decor) (p:BoundPool):QuickPool :=
  (p,ws.countP (fun w => z9 p.dmn w.1),
     ws.all (fun w => availableB p.dmn p.wires w.1))
def fastCost (s:QuickPool) (k:Nat) (a b:Decor) (op:Nat) (ka kb:Bool) :=
  if !s.2.2 then false else
  let p:=s.1
  let un:=op==2
  let const:=fun w:Decor => z9 p.dmn w.1
  let z:=cvv (movedChoice op a b)
  let zm:=masked p.dmn z
  let zc:=z9 p.dmn z
  let cm:=s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free:=zc || zm==masked p.dmn a.1 || zm==masked p.dmn b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {p k ws a b op ka kb} (ha:a∈ws) (hb:b∈ws)
    (h:fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true:=by
  let z:=cvv (movedChoice op a b)
  let const:=fun w:Decor => z9 p.dmn w.1
  let free:=z9 p.dmn z || masked p.dmn z==masked p.dmn a.1 ||
      masked p.dmn z==masked p.dmn b.1
  let rest:=opKeep (op==2) ka kb a b ws
  have ck:=keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all:ws.all (fun w => availableB p.dmn p.wires w.1)=true
  · have hav:=List.all_eq_true.mp all
    have ready:free=true → availableB p.dmn p.wires z=true:=by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,z9,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have exa:(!availableB p.dmn p.wires z).toNat ≤ (!free).toNat:=by
      cases hf:free <;> cases he:availableB p.dmn p.wires z <;> simp_all
    have hs:(rest.map Prod.fst).all (availableB p.dmn p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK:choiceOK p.dmn p.wires (movedChoice op a b)=true:=by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(z9 p.dmn z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.dmn p.wires z).toNat <
      p.bound+(rest.countP const + if z9 p.dmn z then 1 else 0)
    cases hc:z9 p.dmn z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c:NodeContext) (i j op:Nat) (ka kb:Bool) :=
  let a:=z8 c i
  let b:=z8 c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length)
    (h:quickAt c i j op ka kb=true):checkAt c i j op ka kb=true:=by
  have mem (t) (ht:t<c.2.2.1.length):z8 c t ∈ c.2.2.1:=by
    simp [z8,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  have closed:=fastCost_good (mem _ hi) (mem _ hj) ok
  have cut:c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (z8 c i) (z8 c j) c.2.2.1).map Prod.fst)
      (movedChoice op (z8 c i) (z8 c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c:NodeContext) (i j op:Nat) (ka kb:Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h:fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true:=by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b:Batch) (xs:List NodeContext) (i j op:Nat) (ka kb:Bool) :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d:=len==k
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at (k n) (xs:List NodeContext) {i j op:Nat} {ka kb}
    (hi:i<n) (hj:j<n) {q:Nat} (hq:q<xs.length)
    (budget:xs[q].1=k) (arity:xs[q].2.1=n)
    (pass:batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true:=by
  let len:=1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d:=len==k
  have eval:checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !prB (movedDecor op (z8 xs[q] i) (z8 xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (z8 xs[q] i) (z8 xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (z8 xs[q] i) (z8 xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (z8 xs[q] i) (z8 xs[q] j)):=by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small:len>k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (makeBatch k n xs) i
    let b:=laneWire (makeBatch k n xs) j
    let cov:=if d then packedCov (fun c:NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c:NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen:cov = packedCov (fun c => getCov c.2.2.2.1 d) xs:=by
      dsimp only [cov]
      cases d <;> rfl
    have ca:a = _:=laneWire_at k n xs hi
    have cb:b = _:=laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit:combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b:Batch) (xs:List NodeContext) (i j op:Nat) :=
  let f:=batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b:Batch) (xs:List NodeContext) (i:Nat) (js:List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b:Batch) (xs:List NodeContext):List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js
theorem batchRows_at (k n) (xs:List NodeContext) {q:Nat} (hq:q<xs.length)
    (budget:xs[q].1=k) (arity:xs[q].2.1=n) (js:List Nat)
    (bounds:∀ j ∈ js,j<n) (allRows:batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (z8 xs[q])) = true:=by
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
    have opCheck (d:Bool) (pass:batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (z8 xs[q] i) (z8 xs[q] j) d=true:=by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n:Nat) (xs:List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs:List NodeContext} {q} (hq:q<xs.length)
    (hb:xs[q].1=k) (ha:xs[q].2.1=n) (hn:xs[q].2.2.1.length=n)
    (pass:runBatch k n xs=true):testAll xs[q] xs[q].2.2.1=true:=by
  have all:=batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq:(List.range n).map (z8 xs[q]) = xs[q].2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [z8,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g:Forest) (k i:Nat):NodeContext :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bk,ws):=readNode g k i
  let start:=num*(storedLen g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bk a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T:Sig) (c:NodeContext) :=
  let ws:=c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g:Forest) (k i:Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)):=rfl
theorem makeBlock {g k start n} (h:∀ (i:Nat),start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true:=by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g:Forest) (k start n:Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g:Forest) (k start n ar:Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g:Forest) (k start n ar lo len:Nat) :=
  let xs:=contexts g k start n
  let b:=makeBatch k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h:rowCut g k start n ar lo len=true)
    (i:Nat) (l:lo ≤ i) (r:i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h:rowCut g k start n ar lo a=true) (t:rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true:=by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:=List.mem_range.mp hj
  by_cases first:j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h:rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true:=by
  let xs:=contexts g k start n
  have go (lo num:Nat) (eq:lo+num=ar) :
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
theorem cutsBlock {g k start n ar} (hd:header g k start n ar=true)
    (h:rowCut g k start n ar 0 ar=true):block g k start n=true:=by
  apply makeBlock
  intro i lo hi
  let xs:=contexts g k start n
  have hm:contextOf g k i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb:xs[q].1=k:=by rw [e]; rfl
  have ha:xs[q].2.1=ar:=e ▸ one.1
  have hn:xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)
def boxes (g:Forest) (k start n ar lo num:Nat):Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h:boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true:=by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v:=rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g:Forest) (k start n ar rows:Nat):Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem z0 {g k start n ar rows d} (h:cells g k start n ar rows d) :
    block g k start n=true:=by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v:=z2 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f:α → Bool) (xs:List α):Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h:@listPieces α f xs d):xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap:((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i:Nat):Nat:=0xf
def g15l3:Packing:=(1,0,0,0,1,0,0,g15d3)
def g15samples:Array (Bits × Bits):=#[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns:z1 ColumnInfo:=(z1.leaf [])
def g15autos:Array (List Nat):=#[[],[33,48]]
def g15levels:Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index:Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15:Forest:=⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i:Nat):Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i:Nat):Nat:=0x84001e90fd02fd01fa00
def g31l5:Packing:=(3,1,3,0,4,4,0,g31d5)
def g31d6 (i:Nat):Nat:=0x11a20bf
def g31l6:Packing:=(1,0,3,2,4,0,0,g31d6)
def g31samples:Array (Bits × Bits):=#[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns:z1 ColumnInfo:=(z1.fork 2 (z1.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (z1.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos:Array (List Nat):=#[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels:Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index:Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31:Forest:=⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples:Array (Bits × Bits):=#[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns:z1 ColumnInfo:=(z1.leaf [(8,0,39,0,4)])
def g47autos:Array (List Nat):=#[[],[83,32]]
def g47levels:Nat → Packing
  | _ => emptyPacking
def g47index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47:Forest:=⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples:Array (Bits × Bits):=#[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns:z1 ColumnInfo:=(z1.leaf [(16,0,39,0,4)])
def g55autos:Array (List Nat):=#[[],[84]]
def g55levels:Nat → Packing
  | _ => emptyPacking
def g55index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55:Forest:=⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples:Array (Bits × Bits):=#[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns:z1 ColumnInfo:=(z1.leaf [(32,0,31,0,7)])
def g63autos:Array (List Nat):=#[[],[50,65]]
def g63levels:Nat → Packing
  | _ => emptyPacking
def g63index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63:Forest:=⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i:Nat):Nat:=0x120ff
def g111l6:Packing:=(1,0,2,0,1,0,0,g111d6)
def g111samples:Array (Bits × Bits):=#[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns:z1 ColumnInfo:=(z1.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos:Array (List Nat):=#[[],[83,32]]
def g111levels:Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index:Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111:Forest:=⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples:Array (Bits × Bits):=#[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns:z1 ColumnInfo:=(z1.leaf [(4,0,115,0,5)])
def g119autos:Array (List Nat):=#[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels:Nat → Packing
  | _ => emptyPacking
def g119index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119:Forest:=⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i:Nat):Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i:Nat):Nat:=0x82000f487f40bfa03fa00
def g189l6:Packing:=(3,1,3,0,4,4,0,g189d6)
def g189d7 (i:Nat):Nat:=0x1f5859bf
def g189l7:Packing:=(1,0,3,2,4,0,0,g189d7)
def g189samples:Array (Bits × Bits):=#[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns:z1 ColumnInfo:=(z1.fork 4 (z1.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (z1.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos:Array (List Nat):=#[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels:Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index:Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189:Forest:=⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples:Array (Bits × Bits):=#[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns:z1 ColumnInfo:=(z1.leaf [(32,0,95,0,8)])
def g127autos:Array (List Nat):=#[[],[101,66,16]]
def g127levels:Nat → Packing
  | _ => emptyPacking
def g127index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127:Forest:=⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i:Nat):Nat:=0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i:Nat):Nat:=0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i:Nat):Nat:=0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i:Nat):Nat:=0x2c
def g191d6 (i:Nat):Nat:=0x47d6448788a00
def g191l6:Packing:=(1,4,6,0,2,0,0,g191d6)
def g191d7 (i:Nat):Nat:=0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7:Packing:=(28,3,6,0,2,8,0,g191d7)
def g191d8 (i:Nat):Nat:=0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8:Packing:=(100,2,6,5,2,12,0,g191d8)
def g191d9 (i:Nat):Nat:=0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9:Packing:=(12,1,6,7,2,9,0,g191d9)
def g191d10 (i:Nat):Nat:=0x1f3c11ff
def g191l10:Packing:=(1,0,6,4,2,0,0,g191d10)
def g191samples:Array (Bits × Bits):=#[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns:z1 ColumnInfo:=(z1.fork 19 (z1.fork 9 (z1.fork 4 (z1.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (z1.fork 2 (z1.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (z1.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (z1.fork 5 (z1.fork 2 (z1.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (z1.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (z1.fork 2 (z1.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (z1.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (z1.fork 9 (z1.fork 4 (z1.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (z1.fork 2 (z1.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (z1.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (z1.fork 5 (z1.fork 2 (z1.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (z1.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (z1.fork 2 (z1.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (z1.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos:Array (List Nat):=#[[],[84,115],[117,67,32],[116,83,32]]
def g191levels:Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index:Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191:Forest:=⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples:Array (Bits × Bits):=#[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns:z1 ColumnInfo:=(z1.leaf [(8,0,243,0,7)])
def g251autos:Array (List Nat):=#[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels:Nat → Packing
  | _ => emptyPacking
def g251index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251:Forest:=⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples:Array (Bits × Bits):=#[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns:z1 ColumnInfo:=(z1.leaf [(64,0,191,0,11)])
def g255autos:Array (List Nat):=#[[],[84,115],[117,67,32],[116,83,32]]
def g255levels:Nat → Packing
  | _ => emptyPacking
def g255index:Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255:Forest:=⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i:Nat):Nat:=0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i:Nat):Nat:=0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i:Nat):Nat:=0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i:Nat):Nat:=0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i:Nat):Nat:=0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8:Packing:=(25,4,6,0,3,8,0,g383d8)
def g383d9 (i:Nat):Nat:=0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9:Packing:=(91,3,6,5,3,11,0,g383d9)
def g383d10 (i:Nat):Nat:=0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10:Packing:=(41,2,6,7,3,12,0,g383d10)
def g383d11 (i:Nat):Nat:=0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11:Packing:=(6,1,6,6,3,8,0,g383d11)
def g383d12 (i:Nat):Nat:=0x11b280e4ff
def g383l12:Packing:=(1,0,6,3,3,0,0,g383d12)
def g383samples:Array (Bits × Bits):=#[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns:z1 ColumnInfo:=(z1.fork 29 (z1.fork 14 (z1.fork 7 (z1.fork 3 (z1.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (z1.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (z1.fork 3 (z1.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (z1.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (z1.fork 7 (z1.fork 3 (z1.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (z1.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (z1.fork 4 (z1.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (z1.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (z1.fork 15 (z1.fork 7 (z1.fork 3 (z1.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (z1.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (z1.fork 4 (z1.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (z1.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (z1.fork 7 (z1.fork 3 (z1.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (z1.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (z1.fork 4 (z1.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (z1.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos:Array (List Nat):=#[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels:Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index:Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383:Forest:=⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3:Lower (vars 3) (z5 3) 1:=size_of (hints:=1) (by decide +kernel)
def maps3:List (Nat × List Nat):=[]
def known3:=extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3:Known known3:=extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7:Lower (vars 7) (z5 7) 2:=size_of (hints:=257) (by decide +kernel)
def maps7:List (Nat × List Nat):=[]
def known7:=extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7:Known known7:=extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15:graphValid g15 (bsB known7) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s15_3_0:block g15 3 0 1=true:=by
  apply z0 (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3:block g15 3 0 1 = true:=s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15:checkedTables g15 3:=by
  intro k hk
  interval_cases k
  · exact (rfl:block g15 0 0 0 = true)
  · exact (rfl:block g15 1 0 0 = true)
  · exact (rfl:block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15:Lower (vars 15) (z5 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15:List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15:=extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15:Known known15:=extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45:Lower (vars 45) (z5 45) 3:=size_of (hints:=8965) (by decide +kernel)
def maps45:List (Nat × List Nat):=[]
def known45:=extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45:Known known45:=extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51:Lower (vars 51) (z5 51) 3:=size_of (hints:=1) (by decide +kernel)
def maps51:List (Nat × List Nat):=[]
def known51:=extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51:Known known51:=extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31:graphValid g31 (bsB known51) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s31_5_0:block g31 5 0 1=true:=by
  apply z0 (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1:block g31 5 1 2=true:=by
  apply z0 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5:block g31 5 0 3 = true:=(@z2 g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s31_6_0:block g31 6 0 1=true:=by
  apply z0 (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6:block g31 6 0 1 = true:=s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31:checkedTables g31 6:=by
  intro k hk
  interval_cases k
  · exact (rfl:block g31 0 0 0 = true)
  · exact (rfl:block g31 1 0 0 = true)
  · exact (rfl:block g31 2 0 0 = true)
  · exact (rfl:block g31 3 0 0 = true)
  · exact (rfl:block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31:Lower (vars 31) (z5 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31:List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31:=extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31:Known known31:=extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47:Lower (vars 47) (z5 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47:List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47:=extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47:Known known47:=extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55:Lower (vars 55) (z5 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55:List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55:=extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55:Known known55:=extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63:Lower (vars 63) (z5 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63:List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63:=extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63:Known known63:=extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111:graphValid g111 (bsB known63) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s111_6_0:block g111 6 0 1=true:=by
  apply z0 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6:block g111 6 0 1 = true:=s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111:checkedTables g111 6:=by
  intro k hk
  interval_cases k
  · exact (rfl:block g111 0 0 0 = true)
  · exact (rfl:block g111 1 0 0 = true)
  · exact (rfl:block g111 2 0 0 = true)
  · exact (rfl:block g111 3 0 0 = true)
  · exact (rfl:block g111 4 0 0 = true)
  · exact (rfl:block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111:Lower (vars 111) (z5 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111:List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111:=extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111:Known known111:=extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119:Lower (vars 119) (z5 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119:List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119:=extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119:Known known119:=extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189:graphValid g189 (bsB known119) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s189_6_0:block g189 6 0 1=true:=by
  apply z0 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1:block g189 6 1 2=true:=by
  apply z0 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6:block g189 6 0 3 = true:=(@z2 g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s189_7_0:block g189 7 0 1=true:=by
  apply z0 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7:block g189 7 0 1 = true:=s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189:checkedTables g189 7:=by
  intro k hk
  interval_cases k
  · exact (rfl:block g189 0 0 0 = true)
  · exact (rfl:block g189 1 0 0 = true)
  · exact (rfl:block g189 2 0 0 = true)
  · exact (rfl:block g189 3 0 0 = true)
  · exact (rfl:block g189 4 0 0 = true)
  · exact (rfl:block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189:Lower (vars 189) (z5 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189:List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189:=extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189:Known known189:=extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250:Lower (vars 250) (z5 250) 5:=size_of (hints:=1366507616) (by decide +kernel)
def maps250:List (Nat × List Nat):=[]
def known250:=extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250:Known known250:=extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127:Lower (vars 127) (z5 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127:List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127:=extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127:Known known127:=extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191:graphValid g191 (bsB known127) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_6_0:block g191 6 0 1=true:=by
  apply z0 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6:block g191 6 0 1 = true:=s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_7_0:block g191 7 0 13=true:=by
  apply z0 (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1:block g191 7 13 15=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7:block g191 7 0 28 = true:=(@z2 g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_0:block g191 8 0 7=true:=by
  apply z0 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1:block g191 8 7 61=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2:block g191 8 68 32=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8:block g191 8 0 100 = true:=(@z2 g191 8 0 68 32 (@z2 g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_9_0:block g191 9 0 3=true:=by
  apply z0 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1:block g191 9 3 9=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9:block g191 9 0 12 = true:=(@z2 g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_10_0:block g191 10 0 1=true:=by
  apply z0 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10:block g191 10 0 1 = true:=s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191:checkedTables g191 10:=by
  intro k hk
  interval_cases k
  · exact (rfl:block g191 0 0 0 = true)
  · exact (rfl:block g191 1 0 0 = true)
  · exact (rfl:block g191 2 0 0 = true)
  · exact (rfl:block g191 3 0 0 = true)
  · exact (rfl:block g191 4 0 0 = true)
  · exact (rfl:block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191:Lower (vars 191) (z5 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191:List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191:=extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191:Known known191:=extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251:Lower (vars 251) (z5 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251:List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251:=extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251:Known known251:=extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255:Lower (vars 255) (z5 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255:List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255:=extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255:Known known255:=extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383:graphValid g383 (bsB known255) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_8_0:block g383 8 0 23=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1:block g383 8 23 2=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8:block g383 8 0 25 = true:=(@z2 g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_9_0:block g383 9 0 9=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1:block g383 9 9 75=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2:block g383 9 84 7=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9:block g383 9 0 91 = true:=(@z2 g383 9 0 84 7 (@z2 g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_10_0:block g383 10 0 5=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1:block g383 10 5 16=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2:block g383 10 21 20=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10:block g383 10 0 41 = true:=(@z2 g383 10 0 21 20 (@z2 g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_11_0:block g383 11 0 1=true:=by
  apply z0 (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1:block g383 11 1 5=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11:block g383 11 0 6 = true:=(@z2 g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_12_0:block g383 12 0 1=true:=by
  apply z0 (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12:block g383 12 0 1 = true:=s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383:checkedTables g383 12:=by
  intro k hk
  interval_cases k
  · exact (rfl:block g383 0 0 0 = true)
  · exact (rfl:block g383 1 0 0 = true)
  · exact (rfl:block g383 2 0 0 = true)
  · exact (rfl:block g383 3 0 0 = true)
  · exact (rfl:block g383 4 0 0 = true)
  · exact (rfl:block g383 5 0 0 = true)
  · exact (rfl:block g383 6 0 0 = true)
  · exact (rfl:block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383:Lower (vars 383) (z5 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383:List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383:Known known383:=extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i:Nat):Nat:=0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i:Nat):Nat:=0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i:Nat):Nat:=(if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i:Nat):Nat:=0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i:Nat):Nat:=0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i:Nat):Nat:=0x202e0
def deadd8 (i:Nat):Nat:=0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8:Packing:=(2,6,7,0,4,3,0,deadd8)
def deadd9 (i:Nat):Nat:=0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9:Packing:=(25,5,7,1,4,9,0,deadd9)
def deadd10 (i:Nat):Nat:=(if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10:Packing:=(156,4,7,5,4,12,0,deadd10)
def deadd11 (i:Nat):Nat:=(if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11:Packing:=(183,3,7,8,4,14,0,deadd11)
def deadd12 (i:Nat):Nat:=0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12:Packing:=(32,2,7,8,4,12,0,deadd12)
def deadd13 (i:Nat):Nat:=0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13:Packing:=(4,1,7,5,4,8,0,deadd13)
def deadd14 (i:Nat):Nat:=0x17e2b6526070604013ff
def deadl14:Packing:=(1,0,7,2,4,0,0,deadd14)
def deadsamples:Array (Bits × Bits):=#[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns:z1 ColumnInfo:=(z1.fork 63 (z1.fork 31 (z1.fork 15 (z1.fork 7 (z1.fork 3 (z1.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (z1.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (z1.fork 4 (z1.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (z1.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (z1.fork 8 (z1.fork 4 (z1.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (z1.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (z1.fork 4 (z1.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (z1.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (z1.fork 16 (z1.fork 8 (z1.fork 4 (z1.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (z1.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (z1.fork 4 (z1.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (z1.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (z1.fork 8 (z1.fork 4 (z1.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (z1.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (z1.fork 4 (z1.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (z1.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (z1.fork 31 (z1.fork 15 (z1.fork 7 (z1.fork 3 (z1.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (z1.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (z1.fork 4 (z1.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (z1.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (z1.fork 8 (z1.fork 4 (z1.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (z1.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (z1.fork 4 (z1.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (z1.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (z1.fork 16 (z1.fork 8 (z1.fork 4 (z1.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (z1.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (z1.fork 4 (z1.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (z1.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (z1.fork 8 (z1.fork 4 (z1.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (z1.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (z1.fork 4 (z1.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (z1.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos:Array (List Nat):=#[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels:Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex:Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead:Forest:=⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead:graphValid dead (bsB known383) = true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0:block dead 8 0 2=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8:block dead 8 0 2=true:=sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0:block dead 9 0 12=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12:block dead 9 12 13=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9:block dead 9 0 25=true:=(@z2 dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0:block dead 10 0 6=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6:block dead 10 6 36=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42:block dead 10 42 36=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78:block dead 10 78 35=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113:block dead 10 113 36=true:=by
  apply z0 (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149:block dead 10 149 7=true:=by
  apply z0 (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10:block dead 10 0 156=true:=(@z2 dead 10 0 149 7 (@z2 dead 10 0 113 36 (@z2 dead 10 0 78 35 (@z2 dead 10 0 42 36 (@z2 dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0:block dead 11 0 4=true:=by
  apply z0 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4:block dead 11 4 36=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40:block dead 11 40 15=true:=by
  apply z0 (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55:block dead 11 55 36=true:=by
  apply z0 (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91:block dead 11 91 36=true:=by
  apply z0 (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127:block dead 11 127 29=true:=by
  apply z0 (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156:block dead 11 156 27=true:=by
  apply z0 (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11:block dead 11 0 183=true:=(@z2 dead 11 0 156 27 (@z2 dead 11 0 127 29 (@z2 dead 11 0 91 36 (@z2 dead 11 0 55 36 (@z2 dead 11 0 40 15 (@z2 dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0:block dead 12 0 3=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3:block dead 12 3 14=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17:block dead 12 17 15=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12:block dead 12 0 32=true:=(@z2 dead 12 0 17 15 (@z2 dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0:block dead 13 0 1=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1:block dead 13 1 3=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13:block dead 13 0 4=true:=(@z2 dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0:block dead 14 0 1=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14:block dead 14 0 1=true:=sdead14_0
theorem tablesdead:checkedTables dead 14:=by
  intro k hk
  interval_cases k
  · exact (rfl:block dead 0 0 0 = true)
  · exact (rfl:block dead 1 0 0 = true)
  · exact (rfl:block dead 2 0 0 = true)
  · exact (rfl:block dead 3 0 0 = true)
  · exact (rfl:block dead 4 0 0 = true)
  · exact (rfl:block dead 5 0 0 = true)
  · exact (rfl:block dead 6 0 0 = true)
  · exact (rfl:block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
def lowFull:Lower (vars 511) (z5 511) 15 :=
  lower_forest (g:=dead) (prior:=bsB known383) (i:=0) (hints:=0x321032124)
    (before_sound _ valid383) geomdead tablesdead (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
def newKnown:=(511,15)::known383
theorem newValid:Known newKnown:=by
  intro e he
  rcases List.mem_cons.mp he with rfl | hm
  · exact lowFull
  · exact valid383 e hm
def dataNew9 (i:Nat):Nat:=0x1e0fe002f8007e001f8007e001f8007008190207e001c02064081f8007e001f8007e001f8007e001f8007e001f8007e001f8007e001f8007e001f8004c08130204c0813020400000000000000000000000000000000000000000000000000000000000000000000000000000000000035ed333aca316c12f2b82ceaf2aaa62869d2629423e8b21a821f6791d2701ae6718a5e1665514f529455013b4d9314b1274891d4611343909410ff3e8f53c0eb398e1370d7348cd320c32f8b92d0af2a8a52809b25891230872087d1e0731b8691905f168551404b118410f0370c82d0a023078190500f028050035bc34abe1429096abc6a16c285812d5b8d42b850b025eb61a854981544b57a3509e142c096b7861cac5c5212eba4a9aa44dc447b7495327233548bba92a63d876a9175d85495126e112dbb0a9139112a234bb94daa98b084e9b729b552f6429d36e536aa5ec813a6dca6d54bd84274eb94daa96b214e9d729b552d6291d3ae536aa5ac213a79ca6d54ad84274f994daa93b214e9f329b55276109d3ea536aa4ac853a7d8a6d548d90a72f68cd6a153548a7e919aa9b04a91d7d22f57354d522b9ac4ed10c2aa6773d09da21814c4eef813b19a629095df0276224c52139fe16ea7850a42589fa885f2bb694b13f510be1569896e78a217c285212dde14427850a42589fa882f277694b57c510562e2909637c9dd1caeda26c6f93b978d1422d8cfa665f2bb694b19f4ccbe1569896f589557c285212c73d2aad855aa658e7a555b0ab4c4b7e84aa9e14290963dc9551caeda26c7b92a978d1422daf62552b171484b1bb466be1569896f708cd7c285212c76d19ad855aa258eda335b0ab4c4b1fa4668e576d1363f48ccbc68a116d7e119958b8a4250bf9bdb31a82a0a1ef37b6634a52943f66f6cc68ca32dcacc2af845aa672dd97db31a58cca5be2fb6634b0894b3e5b6cc6a2771973cb6d98d44aa32ed96db31a88cc65dd2db66351110da3e5b4aca22772b53cb6959444aa52e796d2b288954ad5b2da565111994bb65b4aca22332b574b69594444452ed96d2b1538ccaddc2da562629095fb05b42c4c5213b4dca6d55444ee76ab94daaa88998ed6729b555112a9daea536aaa22223b5d8a6d554442276cb94daaa77998eda729b554ef2a9db6a536aa9de223b6d8a6d553bc2276e394daaa66954edd529b554cd111dbac536aa99a113b794a6d552ac4476f314daaa55844edf429b55445089cbf8476cc68a22696ec66ceed2c6652df0cd9dda5844a5cf19ad44cd2a8cbb6335a899a331977466b513344434cf8bd9de66694a99f17ad44ef330d3f82f5a288a116
def lvlNew9:Packing:=(98,6,7,0,0,10,0,dataNew9)
def hashNew9 (i:Nat):Nat:=0xa2b0de90519b9aab6d81580052ef280075351290f06b419c0001cad4500040800385000e1252800878afaa58ce001ac72e498f28003ec281ba9275eeecf000830001c0741ad4004d6c58ca22353ba6e0001d4c7a5b845e8633fbde0dc9c9fe2c6bf03a5154f5369a6d9f908428d1c2c38800002db13655e9830b7980008453d0000019f800789a640060fa718abd480094277f0f349000f68001925c20031703200149b8520e000949d04d04d0c018111c28c01d044c480000a2440
def lookupNew9:=lookupWord 25 123 6 11 7 0 hashNew9
def dataNew10 (i:Nat):Nat:=(if i<14 then (if i<7 then (if i<3 then (if i<1 then 0xbc8ce1139fd8bc8ce113cfd8bc8cda26cfd8bc8cda12cfe8bc889a13cef8bc6a2661af78bc6a2556af78bc6a2553af78bc6a2552af78bc6a2551afd8bc6a2336afd8bc6a2332afd8bc6a2331afe8bc6a2226afe8bc6a2223afe8bc6a2221aff0bc6a2113aff0bc6a2112afd8bc69e336afd8bc69e332afd8bc69e331aff0bc69e113aff0bc69e1129ff0bc69a112afd8bc696336afd8bc696332afd8bc696331afe8bc696226afe8bc696223afe8bc696221aff0bc696113aff0bc696112afe8bc68e226aff0bc68a113bed8bc596336bfd0bc54e113bfe0bc54a112e9f8aca22773e9f8aca22772e9f8aca22771eb78aca22553eb78aca22552af78aca22552eb78aca22551ebd8aca22332afd8aca22332ebd8aca22331ebe8aca22223ebe8aca22222ebe8aca22221ebf0aca22113ebd8aca21533ebe8aca21522ebf0aca21511ef58ac956336ef58ac956332afd8ac956332ef58ac956331ef68ac956226ef68ac956223ef68ac956222ef68ac956221ef70ac956113ef70ac956112efc8ac8ce226efc8ac8ce222efc8ac8ce221efd0ac8ce112efe0ac88a113efc8ac889313aef8ac61e662af78ac61e552afd8ac61e332afd8ac616332afd8ac54e332efe0ac4c5212cef8ab5ad536d7d8ab26e332df68a5aed522ff48a58cd522f1f89ca22773b5f89ca22773f3789ca22553b7789ca22553f3d89ca22333b7d89ca22333f3e89ca22223b7e89ca22223f3f09ca22113b7f09ca22113e3f89ca21a53f3d89ca21533f3d89ca21313f7c89c8ce222b7e89c8ce222f7d09c8ce112b7f09c8ce112f7c89c8cd522f7c89c8cd212f7e09c88a113b7f09c88a113e7e89c889a13f7e09c889511f7c89c889313e5f89c6a2772b5f89c6a2772e7789c6a2552e7f09c6a2112e7d89c696331e7e89c696223e7e89c696221e7f09c696113e7e89c68e226b7e89c68e226b7f09c60a112b3f89c609812f6e89c58e226b7e89c58e223f7c89c54e223b7e89c54e223f7d09c54e113b7f09c54e113edd87c696332edf07c696112dde87baed522ecf86c6a2771ee786c6a2551eed86c6a2331eee86c6a2221fb585ca21533ff485c8cd522ff605c889511ef585c6a1533ef705c6a1511ff483c956223ff503c956113ff482c956332ff602c956112ffc02c4c5213fbd01ca21313ff501c956331ff601c956221ffc01c8cd212ffc01c889313bf701c69a552bfd01c69a332ef701c695512efe01c68a226efd01c689313ff601c549512bde17c2852128ef96c2ad512bfc13c2852128ef96c2ad3128ef96c2ad532afe0ac5c52128ef96c2ae8828df97caeda528df97c2ad3128ef96caeda818ff11caeda26aaf96c2ae8828df8bc9dda528ef8bc6a26618ff0bc68a116abb94caaa883adb94caaa773aeb94caaa663af394caaa553afa94caaa223afb14caaa113 else (if i<2 then 0xe551bdf17c0ca116bd797c06e552df6975aed522ff49758cd522ff617554a112af796caaa552afd96caaa332eaf96c2ae882baf96c2ae882af796c2ae553af796c2ae552afd96c2ae332afe96c2ae223bed96c296332bed96c216332bed96c216331bee96c216222bee96c216221bef16c216112bee96c20e222bee96c20e221bef16c20e112bef16c20e111bef16c16e112bef16c0ee112baf96c0ae881de7965aed516df7165aed511fe59658cd516ff51658cd511fe6965889516ff6165889511eee9652ae226eee9632ae226cf795caeda529ef95caed6369fd95caed313abf95caaa882aef95caaa662afd95caaa332abf95c2ae883abf95c2ae882abf95c2ae881afd95c2ae336afd95c2ae331afe95c2ae226afe95c2ae223afe95c2ae221aff15c2ae113bf695c20e222bf695c20e221bf715c20e112bf715c20e111bfd15c0ee113bf715c0ca116bfe15c0ae112cf795b16da83cf795b16da81cf795b16da23cf795b16da13df5953aed523df6953aed522ff49538cd522ff495354a223ff515354a113ff615354a112f7c95326e223ff495316e223df6952aed512df7152aed511ff6152889511efe152684a12ff6152546112f7e15226e112ff615216e112bfa94c216222bfa94c216221bfb14c216112bfa94c20e222bfa94c20e221bfb14c20e112bfb14c20e111bfb14c14a116bfb14c0ca116cfd93caeda83cfd93caeda239ef93caed656abf93caaa882aef93caaa662af793caaa552abf93c2ae882abf93c2ae881afe93c2ae226afe93c2ae221bf693c295522bfc93c216222bfc93c216221bfd13c216112cfd93b0eda81cfd93b0eda52dfd131aed213dfe131aed212cfe92caeda82abf92c2ae883abf92c2ae881af792c2ae556af792c2ae553af792c2ae551afd92c2ae336afd92c2ae331aff12c2ae113b3f92c26e883afe92c22eaa2bfc92c216331bfe12c20e111afe92c16eaa2afe92c0eeaa2cfe92b0ada83cfe92b0ada81cfe92b0ada53cfe92b0ada13cff11caeda819fd91caed5339fe91caed522abf91caaa882aef91caaa662af791caaa552afd91caaa332abf91c2ae883abf91c2ae882af791c2ae553af791c2ae552afd91c2ae332afe91c2ae223bfd11c216332bfe11c216222bfe11c20e222bf591c0ee553bf691c0ae552cff11b06da83cff11b06da53cff11b06da52cff11b06da23abf8bcaaa882cbf8bca21a73cbf8bca21a72cbf8bca21a71cbf8bca21a53cbf8bca21a52cbf8bca21a51cbf8bca21a23cbf8bca21a13cbf8bca21a12adf8bc9dda529df8bc9dda529df8bc9dd5269df8bc9dd5219ef8bc999812df58bc9563339fd8bc956333df68bc9562229fe8bc956222cf78bc955a36cf78bc955a26cf78bc955a23cf78bc955a13cf78bc955a12de78bc955636df58bc955313df68bc955212bfd0 else 0xafd9ac5d6336afd9ac5d6332afd9ac5d6331aff1ac5d6112aff1ac5d6111aff1ac5c6112af79ac22e552afd9ac22e332afe9ac22e221aff1ac22e112afd9ac216332afd9ac216331afe9ac216222afe9ac216221aff1ac216112afe9ac20e222afe9ac20e221aff1ac20e112aff1ac20e111abf9ac16e881afd9ac16e336afd9ac16e332afd9ac16e331afe9ac16e226afe9ac16e221aff1ac16e112afe9ac14e226afe9ac14e222afe9ac14e221aff1ac14e112af79ac0ee556af79ac0ee552af79ac0ee551aff1ac0ee112abf9ac0ae881af79ac0ae556af79ac0ae551afd9ac0ae331af79ac06e552afd9ac06e332cbf9a8aed812cfd9a8aed533cfe9a8aed522cff1a8aed511e9f9a8a22772eb79a8a22552ebd9a8a22332ebe9a8a22222ebf1a8a22112ecf9a89de662ecf9a89de661ed79a89de556ed79a89de552edd9a89de336edd9a89de332ede9a89de226edf1a89de116edf1a89de112ee79a899a552ee79a899a551eed9a899a332eed9a899a331eee9a899a222eee9a899a221eef1a899a112ef59a8956336ef59a8956332ef69a8956226ef69a8956222ef71a8956116ef71a8956112efc9a88ce226efc9a88ce222efd1a88ce116efd1a88ce112efe1a888a116efe1a888a112eb79a82a2552ebd9a82a2332e7d9a826e332ebf1a822e112ef59a80ee553ef69a80ae552ef71a806e551cfd9a7aed533cff1a7aed511ee79a799a552ee79a799a551eed9a799a332eed9a799a331eee9a799a221eef1a799a112ef59a7956336ef59a7956332ef59a7956331ef71a7956116ef71a7956112ef71a7956111efc9a78ce226efc9a78ce221efd1a78ce116efd1a78ce112efd1a78ce111efe1a788a116efe1a788a111cf79a5aed516cf79a5aed512ef59a5956336ef59a5956331ef69a5956226ef69a5956221ef71a5956116efc9a58ce226efc9a58ce221efd1a58ce116efd1a58ce111efe1a588a116efe1a588a111ef59a5296332ef71a516e112cfd9a3aed316cfd9a2aed313cfe9a2aed216efe1a288a116efd1a20ee113cbf98caeda82afe98caa9522af798c2ae556af798c2ae553af798c2ae552af798c2ae551afd98c2ae336afd98c2ae332afd98c2ae331afe98c2ae223aff18c2ae113aff18c2ae112b7e98c26e223bbf18c0ca116cbf98b22da53cbf98b22da52cbf98b22da23cbf98b22da13df5985aed533ff498554e223ff518554e113fb598522d533dfd181aed313fbd18122d313dde97caed522abf97c2ae883abf97c2ae882abf97c2ae881afd97c2ae336afd97c2ae332afd97c2ae331aff17c2ae113aff17c2ae112bde97c22e221bdd97c216332bdd97c216331bde97c216222bde97c216221bdf17c216112bde97c20e222bde97c20e221bdf17c20e112bdf17c20e111bd797c0ee556bd797c0ee552bd797c0e)) else (if i<5 then (if i<4 then 0x6626e332d6fa6626e332f6ea6626e223d6fa6626e223f6ea6626e221d6fa6626e221e6fa6626da53e6fa6626da51f6da6626d533d6fa6626d533f6f26626d511ecfa661eda52fe5a660ee553fe6a660ae552cf7a55aeda26cf7a55aeda12de7a55aed636df5a55aed313df6a55aed212ff4a558ce226ff4a558ce222ff4a558ce221ff52558ce116ff52558ce112ff52558ce111ef5a558cda16ef5a558cda12ff625588a116ff625588a112ff625588a111ef6a55889a16ef6a55889a12cf7a556ad816cf7a556ad516cf7a556ad216cf7a556ac832cf7a556ac831cf7a556ac821cf7a556ac812cf7a556ac326cf7a556ac321cf7a556ac312ef5a5568ca32ef725568a116ef7255686112ef7255684a12db7a5562ca12db7a5562c326db7a5562c321ff5255605313dd7a555eca32dd7a555eca12dd7a555ec832dd7a555ec831dd7a555ec812dd7a555ec326dd7a555ec321ff62555c5212de7a555aca32de7a555aca12de7a555ac832de7a555ac831de7a555ac321df3a5552ca12df3a5552c832df3a5552c831df3a5552c812df3a5552c326df3a5552c321df5a554eca12ff52554c5213ff62554c5212df6a554ac831df725546c832df725546c326ef5a552ae336ef5a552ae332cf7a552ae332ef5a552ae331ef6a552ae226ef6a552ae223ef6a552ae221ef72552ae113ef72552ae112cf7a552ae112cf7a552ad832cf7a552ad532ff6255285212f75a5526e332d77a5526e332f76a5526e223d77a5526e223f76a5526e221d77a5526e221f7725526e112d77a5526e112e77a5526da36d77a5526da36e77a5526da13d77a5526d822f67a5526d636d77a5526d633f75a5526d313d77a5526d313d77a5526d311ff52550ee113ff62550ae112ef725506da26cfda33aeda26cfda33aeda12dfca33aed522dfd233aed511dfca33aed212ffc23388a116ffc23388a112ffc23388a111efca33889a16efca33889a12cfda336ad816cfda336ad716cfda336ad712cfda336ad516cfda336ad216cfda336ac821cfda336ac812cfda336ac526cfda336ac521cfda336ac512efd23368a116efd233686112efd233684a12dbda3362ca12ddda335eca12ddda335ec812ffc2335c5212deda335aca12deda335ac521df5a3356ca12ff4a33549512ff5233549511ffc2334c5212efca332ae226efca332ae221efd2332ae112cfda332ae112cfda332ad312ffc233285212f7ca3326e223d7da3326e223f7ca3326e221d7da3326e221f7d23326e112d7da3326e112f7d23326d511d7da3326d511ffc2330ae112efd23306da26dfe222aed511dfca22aed313cfea226ad816cfea226ad516cfea226ad216ffc222605313ffc2224c5213efe2222ae113f7e22226d511d7ea2226d511ffc2220ee113af79ac616556afd9ac616336afe9ac616226 else 0xd511f3da8826d313d3fa8826d313d3fa8826d311e9fa881eda52fb5a880ee553fbd2880ee113fb6a880ae552fbe2880ae112fb728806e551dbf28806da62cdfa77aeda56cdfa77aeda51cdfa77aeda26cdfa77aeda12dcfa77aed656dcfa77aed636ddda77aed533ddea77aed522ddf277aed511ddda77aed313ddea77aed212fc7a7799a552fc7a7799a551fcda7799a332fcda7799a331fcea7799a221fcf27799a112ecfa77999a52ecfa77999a51ecfa77999a12fd5a77956336fd5a77956332fd5a77956331fd6a77956226fd6a77956221fd7277956116fd7277956112fd7277956111ed7a77955a16ed7a77955a12fdca778ce226fdca778ce221fdd2778ce116fdd2778ce112fdd2778ce111edda778cda16edda778cda12fde27788a116fde27788a111edea77889a16cdfa776ad856cdfa776ad816cdfa776ad516cdfa776ad216cdfa776ac832cdfa776ac831cdfa776ac812cdfa776ac312edda77696336edda77696332edda77696331edea77696226edea77696221edf277696116edf277696112edf277696111edf27768a116edf277686112fd5a77615533fdd277605313dcfa775ac832dcfa775ac831fc7a77595516fd7277595511dd7a7756c832dd7a7756c831fd5a7754d523fd6a7754d522fd6a77549512fd7277549511ddba7752c832ddba7752c831ddba7752c812fdd2774c5213fde2774c5212ddea774ac831ddf27746c832edda772ae336edda772ae332edda772ae331edf2772ae113edf2772ae112f5da7726e332d5fa7726e332f5f27726e112d5fa7726e112e5fa7726da53e5fa7726da51e5fa7726da36d5fa7726da36e5fa7726da13f4fa7726d636d5fa7726d633f5da7726d533d5fa7726d533f5f27726d511d5fa7726d511f5da7726d313d5fa7726d313d5fa7726d311fdd2770ee113ddf27706da62edf27706da26cefa66aeda52cefa66aeda51cefa66aeda12deda66aed533deea66aed522def266aed511deda66aed313deea66aed212fe5a66956332fe5a66956331fe6a66956222fe6a66956221fe7266956112ee7a66955a12feca668ce222feca668ce221fed2668ce112eeda668cda12fee26688a112eeea66889a12cefa666ad752cefa666ad751cefa666ad712cefa666ac532cefa666ac531cefa666ac521cefa666ac321ee7a66696551eeda66696331eeea66696221ee7a66694a52eeda6668ca32dafa6662c321fe5a66615533fed266605313dcfa665eca32dcfa665ec321fe6a665d5522de7a6656c321fe5a6654d523fe6a6654d522fe6a66549512fe7266549511deba6652ca52deba6652c521deba6652c321fed2664c5213fee2664c5212ee7a662ae553ee7a662ae552cefa662ae552eeda662ae332cefa662ae332eeea662ae223cefa662ad852cefa662ad832fe6a66295522f6da) else (if i<6 then 0xcfeaaa56d212efcaaa54e223efd2aa54e113ef5aaa54d523ef6aaa54d522efe2aa54a112ef6aaa549512ef72aa549511cfdaaa4ec813cfdaaa4ec523cfdaaa4ec513efd2aa4c6113efd2aa4c5213efe2aa4c5212cfeaaa4ac532e7daaa26d533e7daaa26d313cbfa88aeda71cbfa88aeda52cbfa88aeda51cbfa88aeda12dbda88aed533dbea88aed522dbf288aed511dbda88aed313dbea88aed212f8fa889de662f8fa889de661f97a889de556f97a889de552f97a889de551f9da889de336f9da889de332f9da889de331f9ea889de226f9ea889de221f9f2889de116f9f2889de112f9f2889de111e9fa889dda56e9fa889dda52e9fa889dda51e9fa889dda16e9fa889dda12fa7a8899a552fa7a8899a551fada8899a332fada8899a331faea8899a222faea8899a221faf28899a112eafa88999a51eafa88999a12fb5a88956336fb5a88956332fb5a88956331fb6a88956226fb6a88956222fb6a88956221fb7288956116fb7288956112fb7288956111eb7a88955a16eb7a88955a12fbca888ce226fbca888ce222fbca888ce221fbd2888ce116fbd2888ce112fbd2888ce111ebda888cda16ebda888cda12fbe28888a116fbe28888a112fbe28888a111ebea88889a16ebea88889a12cbfa886ad752cbfa886ad751cbfa886ad712cbfa886ac532cbfa886ac531cbfa886ac521cbfa886ac512cbfa886ac321cbfa886ac312eafa8869e662eafa8869e661eb7a8869e556eb7a8869e552eb7a8869e551ebda8869e336ebda8869e332ebda8869e331ebea8869e226ebea8869e221ebf28869e112ebf28869e111eb7a88696556eb7a88696551ebda88696336ebda88696331ebea88696226ebea88696221ebf288696111eb7a88694a52ebda8868ca32ebf288686112ebf288684a12fb5a88615533fbd288605313d9fa885eca32d9fa885eca12d9fa885ec326d9fa885ec321fb6a885d5522fbe2885c5212dafa885aca52dafa885aca32dafa885aca12dafa885ac521dafa885ac321fb7288595511db7a8856ca12db7a8856c326db7a8856c321fb5a8854d523fb6a8854d522fb6a88549512fb7288549511dbba8852ca52dbba8852ca12dbba8852c526dbba8852c521dbba8852c326dbba8852c321dbda884eca12fbd2884c5213fbe2884c5212dbf28846c326eb7a882ae556eb7a882ae553eb7a882ae552cbfa882ae552eb7a882ae551ebda882ae336ebda882ae332cbfa882ae332ebda882ae331ebea882ae226ebea882ae223ebea882ae221ebf2882ae113ebf2882ae112cbfa882ae112cbfa882ad872fb6a88295522fbe288285212f3da8826e332d3fa8826e332f3ea8826e223d3fa8826e223f3ea8826e221d3fa8826e221f3f28826e112d3fa8826e112e3fa8826da51e3fa8826da13d3fa8826d633f3f28826d511d3fa8826 else 0x9c46da83a7f89c46da82a7f89c46da52b7d89c46d533b7e89c46d522c7f89baeda82c7f89baeda53c7f89baeda13c7f89baa9a82d7d89b56d313d7d89b4ed513d7d89b46d533baf88c5ad536cdf88b1eda52cdf87c6ad852cdf87c6ad512fde07c54a112fd687c549512fd707c549511cdf87b46da52cef86c6ad851cef86c6ad812fed06c605313cef86b56da81cef86b4ada81cef86b0eda81ef685c6a1522ff482c54d523ebf01c6a1812bef01c699652bef01c699632adfacc6a2772adfacc6a2771aefacc6a2662af7acc6a2552af7acc6a2551afdacc6a2332afdacc6a2331afeacc6a2222afeacc6a2221aff2cc6a2112abfacc6a1812afdacc6a1533afeacc6a1522aff2cc6a1511abfacc6a0a82aefacc69e661afdacc69e331aff2cc69e111af7acc696556afdacc696336afdacc696332afdacc696331afeacc696226afeacc696221aff2cc696112af7acc695512af7acc694a52afdacc68ca32afeacc68a226afdacc6893139bfacc62ca129bfacc62c3269bfacc62c321be7acc615656bf5acc615533bedacc60d636bfd2cc6053139dfacc5ec8329dfacc5ec8319dfacc5ec812bfe2cc5c52129efacc5aca529efacc5aca329efacc5ac5219efacc5ac321bedacc596336beeacc596226bf72cc595511beeacc58e2269fdacc56d3139feacc56d2129f7acc56ca129f7acc56c8329f7acc56c8319f7acc56c3269f7acc56c321bfcacc54e223bfd2cc54e113bf5acc54d523bf6acc54d522bfe2cc54a112bf6acc549512bf72cc5495119fdacc4eca129fdacc4ec8529fdacc4ec8519fdacc4ec8139fdacc4ec523bfd2cc4c5213bfe2cc4c52129feacc4ac8529feacc4ac8519feacc4ac8329feacc4ac8319feacc4ac5329ff2cc46c8529ff2cc46c8329ff2cc46c8319ff2cc46c326af7acc2ae552afdacc2ae332e9faaaa22773e9faaaa22771eafaaaa22663eafaaaa22662eb7aaaa22553eb7aaaa22552eb7aaaa22551ebdaaaa22332ebdaaaa22331ebeaaaa22223ebeaaaa22221ebf2aaa22113ebf2aaa22112ebdaaaa21533ebeaaaa21522ebf2aaa21511ebdaaaa21313ebeaaaa21212ecfaaa9de663ed7aaa9de553ed7aaa9de551eddaaa9de331edeaaa9de223edeaaa9de221edf2aa9de113eddaaa9dd533edf2aa9dd511eddaaa9dd313ee7aaa99a553ee7aaa99a552eedaaa99a332eeeaaa99a223eef2aa99a113eef2aa99a112eedaaa999533eeeaaa999522eedaaa999313eeeaaa999212ef5aaa956332ef5aaa956331ef6aaa956223ef6aaa956221ef72aa956113ef72aa956112ef5aaa955533ef6aaa955522ef5aaa955313ef6aaa955212efcaaa8ce221efd2aa8ce112efcaaa8cd522efd2aa8cd511efcaaa8cd212efe2aa88a113efe2aa889511efcaaa889313ef5aaa615533efd2aa605313cfdaaa56d313))) else (if i<10 then (if i<8 then 0x1a528ff8bca21a238ff8bca21a139df8bc9dd523bde8bc9dd5229ef8bc9998138ff8bc955a368ff8bc955a268ff8bc955a238ff8bc955a139ef8bc9556369fd8bc9553138ff8bc8cda269fd8bc8cd8238ff8bc889a138ff8bc6a25568ff8bc6a25538ff8bc6a25528ff8bc6a25518ff8bc6a23368ff8bc6a23328ff8bc6a23318ff8bc6a22268ff8bc6a22238ff8bc6a22218ff8bc6a21138ff8bc6a2112cbf8bc6a18128ff8bc6a1531cfe8bc6a15228ff8bc6a13168ff8bc69e3368ff8bc69e3318ff8bc69e1138ff8bc69d8268ff8bc69d8238ff8bc69d8218ff8bc69d6318ff8bc69d5368ff8bc69d5318ff8bc69d3168ff8bc6963368ff8bc6963328ff8bc6962268ff8bc6962238ff8bc6961138ff8bc6961128ff8bc6958268ff8bc6958238ff8bc6956328ff8bc6953168ff8bc6953128ff8bc68e2268ff8bc68d8268ff8bc68a1138ff8bc61da568ff8bc61da538ff8bc61da368ff8bc61da268ff8bc61da238ff8bc61da139ef8bc61d6569ef8bc61d6368ff8bc609a139ef8bc5963369ef8bc5958269ef8bc58d8269fd8bc54e1139fe8bc54a112ebf0aca22112afe8aca21522afd8ac596332afd8ac58e332ef68ac54d522afe8ac54d522cff0a16ad81297f89caed82397f89caed312a7f89ca21a53b3f89ca21853b7d89ca21533b7d89ca21313b7e89c8cd522b7d89c8cd312b7e89c8cd212a7f89c889a13b7f09c889511b7d89c889313b7e89c88921397f89c6ad872c7f89c6ad852c7f89c6ad851c7f89c6ad813c7f89c6ad812c7f89c6ad523c7f89c6ad512e3f89c6a1812e7e89c6a1522b7e89c6a1522b7e89c6a1212b7d89c699533b7d89c695313a7f89c62da52a7f89c62da51a7f89c62da13a7f89c62da1297f89c62d73397f89c62d71197f89c62d633b7e89c62d52297f89c62d522b7f09c62d51197f89c62d511b7d89c62d31397f89c62d31397f89c62d311b7e89c62d21297f89c62d21297f89c62d211a7f89c5eda83a7f89c5eda82a7f89c5eda81a7f89c5eda53a7f89c5eda51a7f89c5eda1397f89c5ed633b7d89c5ed53397f89c5ed533b7f09c5ed51197f89c5ed511b7d89c5ed31397f89c5ed31397f89c5ed311a7f89c5ada83a7f89c5ada53a7f89c5ada52a7f89c5ada51a7f89c5ada23b7d89c5ad53397f89c5ad533b7e89c5ad52297f89c5ad522b7f09c5ad51197f89c5ad32397f89c5ad322a7f89c56da82a7f89c56da81a7f89c56da23a7f89c56da1297f89c56d32397f89c56d322d7d89c56d313b7d89c56d31397f89c56d311d7e89c56d212b7e89c56d21297f89c56d21297f89c56d211f7589c54d523b7f09c546113b7d89c545313a7f89c4eda81a7f89c4eda52a7f89c4eda51b7e89c4ed522b7f09c4ed511a7f89c4ada81a7f89c4ada53a7f89c4ada51b7d89c4ad533b7f09c4ad511a7f8 else (if i<9 then 0xfe7165956116fec9658ce226fed1658ce116fee16588a116f7716526d511ded963aed316fec9638ce226fed1638ce116fee16388a116fec963889316ffc1624c52138ff95caeda838ff95caeda828ff95caeda818ff95caeda368ff95caeda268ff95caeda238ff95caeda13bfd15c4c6113bfe15c4861128ff95c2ae882afd95c2ae332aff15c2ae1128ff95c2ad8328ff95c2ad8128ff95c2ad6328ff95c2ad312bf715c285812af795c20da12bf715c209511af795c0c9a16cf795b16da82ffc15388a113ff4953609523ff49535c9523df595356c823df595356c813d7d95326e332d7d95326e223d7d95326d513d7d95326d313ff49530ed522ff6152605512df69525ed512df595256d313df695256d312df695256c812df695256c312d7e95226e223d7e95226e221d7e95226e112f7715226d511d7f15126e112d7f15126d311cfb94caeda83cfb94caeda53cfb94caeda23cfb94caeda13afb94caaa883afb94caaa553afb94caaa223afb94caaa113afb94caa9873afb94caa9863afb94caa9853afb94caa9823afb94caa9763afb94caa9753afb94caa9723afb94caa9713afb94caa9653afb94caa9623afb94caa9613afb94caa9513afb94caa9213afb94caa8823afb94caa8513afb94c22eaa2afb94c215a12afb94c20da12afb94c16da82afb94c149a16afb94c0c9a16afb94c06da828ff93caeda828ff93caeda818ff93caeda718ff93caeda568ff93caeda528ff93caeda268ff93c2ae882af793c2ae556af793c2ae552af793c2ae551aff13c2ae1128ff93c2ad8728ff93c2ad8528ff93c2ad8128ff93c2ad6528ff93c2ad512bfd13c285812d7d93c26d513afd93c215a12bbd93c16e883bfd13c16e113bfd13c14a113bf593c06e553bfc93c06e223cfd93b0eda828ff92caeda838ff92caeda818ff92caeda568ff92caeda538ff92caeda368ff92caeda1397f92c26e88397f92c26d633b7d92c26d53397f92c26d53397f92c26d513b7f12c26d51197f92c26d511bfc92c216333bfc92c216332bfe12c216113bfe12c216112bfe12c20e112bbe92c16e882bfc92c16e332bfe12c16e112bfe12c14e112bbe92c06e882bf692c06e552bfc92c06e3328ff91caeda838ff91caeda828ff91caeda739ff11caeda628ff91caeda538ff91caeda528ff91caeda2397f91c26d822aff11c22eaa2bfd11c216333bfd11c216331bfe11c216223bfe11c216221bfe11c20e221bfd11c209313bbf11c16e881bfd11c16e331bfe11c16e221bfe11c14e221bfe11c14d212bfd11c149313cff11b06da82abf8bcaaa8838ff8bcaaa882abf8bcaaa881af78bcaaa553af78bcaaa552afe8bcaaa223aff0bcaaa1138ff8bcaa98718ff8bcaa96328ff8bcaa95328ff8bcaa93128ff8bca21a738ff8bca21a718ff8bca21a538ff8bca2 else 0xa846c326ebf1a8285812c7f9a826e332ee79a799a553eed9a799a333eee9a799a223eef1a799a113ecf9a7999732ecf9a7999712eed9a7999533eee9a7999522eef1a7999511ef59a7956333ef71a7956113efc9a78ce223efd1a78ce113edd9a78cd716edd9a78cd712efc9a78cd522efd1a78cd511efe1a788a113ef59a7615533edd9a75ce332edf1a75ce112edf1a75c6112cef9a75ac832cef9a75ac831eed9a7596336cf79a756c832cf79a756c831efd1a754e113efe1a754a112cfb9a752c832cfb9a752c831cfb9a752c812cfe9a74ac831cff1a746c832cff1a706da62ef59a5956333ef59a5956332ef69a5956223ef69a5956222ef71a5956113ef71a5956112efc9a58ce223efc9a58ce222efd1a58ce113efd1a58ce112ef59a58cd516ef59a58cd512efe1a588a113efe1a588a112ef69a5889516ef69a5889512cbf9a562c326cbf9a562c321cdf9a55ec831cdf9a55ec326cdf9a55ec321ef71a55c5512cef9a55ac831cef9a55ac321ef71a5546112cfb9a552c831cfb9a552c326cfb9a552c321cfe9a54ac831cff1a546c326efc9a38ce226efd1a38ce116efe1a388a116efc9a3889316efd1a34c5216efe1a3285212efe1a288a113eee9a2889616efc9a2889313efd1a24c61138ff98caeda738ff98caeda718ff98caeda538ff98caeda528ff98caeda238ff98caeda13aef98caaa662af798caaa552afd98caaa3328ff98c2ae5528ff98c2ae332afe98c2ae226afe98c2ae2218ff98c2ae1128ff98c2ad7328ff98c2ad7128ff98c2ad6528ff98c2ad6328ff98c2ad5328ff98c2ad5128ff98c2ad31297f98c26e22397f98c26d63397f98c26d513b7d98c26d31397f98c26d313abf98c0c9a16cdf98b1eda52fa7987615656fb5987615533fd69875d5522fde1875c5212cdf9872ad732cdf9872ad712fbd186605313fe7186595511fe5985596336fe6985596226fec98358e226fad98358d826ff498354d522faf182605616fbd182605313ff6182549511dfd18156d313cff1812ae112f7d18126d313cdf97caeda529df97caeda529df97caed5269df97caed5229df97caed521adf97c2ad312adf97c22eaa2bde97c22e223bdd97c216333bde97c216223bdf17c216113adf97c215a12adf97c20da12adf97c0eda82adf97c0c9a16bd797c06e553adf97c06da82fde1765c5212fe7176595511ff6172549511dfe171aed212dfe17156d212cef96caeda819ef96caeda819ef96caed8129ef96caed811bf716c549511aef96c2ad532aef96c2ad312bed96c216333bee96c216223bef16c216113aef96c215a12aef96c20da12bed96c16e336bee96c16e226bef16c16e113aef96c16da82bee96c14e226bef16c14a113be796c0ee556bee96c0ee226aef96c0eda82baf96c0ae883fe5965956336fe6965956226)) else (if i<12 then (if i<11 then 0xda128ff9acaed8728ff9acaed8718ff9acaed6328ff9acaed6318ff9acaed5328ff9acaed3128ff9ac62c5328ff9ac62c512cbf9ac62c3268ff9ac62c312aef9ac61e662afd9ac61e336afd9ac61e332aff1ac61e112af79ac616553af79ac616552af79ac616551afd9ac616333afd9ac616332afd9ac616331afe9ac616223afe9ac616222afe9ac616221aff1ac616113aff1ac616112aff1ac616111afd9ac60e336afe9ac60e226afe9ac60a226afe9ac60a223aff1ac60a113aff1ac606112afd9ac5d6333aff1ac5d6113afd9ac5ce336aff1ac5ca113cf79ac56c8318ff9ac56c8318ff9ac56c821cf79ac56c326cf79ac56c3218ff9ac56c321aff1ac546113aff1ac546112cfe9ac4ac851cfe9ac4ac831aff1ac486113cff1ac46c852cff1ac46c832cff1ac46c326af79ac22e553af79ac22e551afd9ac22e331afe9ac22e223aff1ac22e113afd9ac216333afe9ac216223aff1ac216113aff1ac20a113abf9ac16e883abf9ac16e882afe9ac16e223aff1ac16e113aff1ac14a113abf9ac0ee882abf9ac0ee881afe9ac0ee226afe9ac0ee221abf9ac0ae883af79ac0ae553afd9ac0ae336aff1ac0ae113abf9ac06e883abf9ac06e882af79ac06e553afe9ac06e223cdf9ab1ed521cef9ab1ad812cfd9ab0ed823e9f9a8a22773e9f9a8a22771eb79a8a22553eb79a8a22551ebd9a8a22333ebd9a8a22331ebe9a8a22223ebe9a8a22221ebf1a8a22113ebf1a8a22111ebd9a8a21533ebe9a8a21522ebf1a8a21511ecf9a89de663ed79a89de553ed79a89de551edd9a89de333edd9a89de331ede9a89de223ede9a89de221edf1a89de113edf1a89de111e9f9a89dd816e9f9a89dd812ecf9a89dd656ecf9a89dd636edd9a89dd533ede9a89dd522edf1a89dd511ee79a899a553eed9a899a333eee9a899a223eef1a899a113eaf9a8999812eed9a8999533eee9a8999522eef1a8999511ef59a8956333ef59a8956331ef69a8956223ef69a8956221ef71a8956113ef71a8956111eb79a8955816eb79a8955812ee79a8955636ef59a8955533ef69a8955522ef71a8955511efc9a88ce223efc9a88ce221efd1a88ce113efd1a88ce111ebd9a88cd816ebd9a88cd812efc9a88cd522efd1a88cd511efe1a888a113efe1a888a111ebe9a8889816ebe9a8889812efe1a8889511ebf1a8606112ebf1a8605612ebf1a8605312cdf9a85eca32cdf9a85eca12cdf9a85ec326ef69a85d5522cef9a85aca52cef9a85aca32cef9a85aca12ee79a8596556eed9a8596336eee9a8596226ef71a8595511eed9a858e336eee9a858e226cf79a856ca12cf79a856c326efc9a854e223efd1a854e113ef69a854d522efe1a854a112ebe9a8549812ef69a8549512cfb9a852ca52cfb9a852ca12cfb9a852c526cfb9a852c326cfd9a84eca12cff1 else 0xcefa666ad823cefa666ad812cefa666ad753cefa666ad723cefa666ad513cefa666ad512cefa666ad213cefa666ac523ee7a66696553ee7a66696552eeda66696333eeda66696332eeea66696223eeea66696222eef266696113eef266696112ee7a66695512eeea6668a223eef26668a113eeda66689313fee2665c5212deda6656d313deea6656d212feca6654e223fed26654e113fee26654a112deda664ec523deea664ac532def26646c531def26646c521def26646c321cefa662ad732cefa662ad532d6fa6626d513fcea661ed522cf7a55aeda36cf7a55aeda23cf7a55aeda13ff4a558ce223ff52558ce113ef5a558cda26ef5a558cda23ef5a558cda13fe5a558cd616ff4a558cd522ff52558cd511ff4a558cd212ff625588a113ef6a55889a13fe6a55889616ff6255889511ff4a55889313cf7a556ad836cf7a556ad826cf7a556ad823cf7a556ad812cf7a556ad513cf7a556ad512cf7a556ad316cf7a556ad213cf7a556ac823cf7a556ac813cf7a556ac213ef5a5568e336ef6a5568e226ef725568e116ef5a5568d316ef6a5568a226ef6a5568a223ef725568a113ee7a55689616ef5a55689313ef6a55689216ef7255686113db7a5562c213fe5a5560d636fe7255605616dd7a555ec813dd7a555ec213de7a555ad516de7a555ad316de7a555ac326de7a555ac213fe5a5558e336fe6a5558e226fe725558e116fe5a5558d316df5a5556d313df6a5556d212ff4a5554e223ff525554e113ff625554a112df5a554ec813ff52554c6113df6a554ac832df6a554ac812df6a554ac312ff6255486112df725546c831df725546c321cf7a552ad812cf7a552ad732cf7a552ad712cf7a552ad632d77a5526d513cfda33aeda23cfda33aeda13ffc23388a113efca33889a13feca33889616ffc233889511cfda336ad826cfda336ad823cfda336ad812cfda336ad726cfda336ad723cfda336ad513cfda336ad512cfda336ad316cfda336ad213cfda336ac823cfda336ac813cfda336ac523cfda336ac513cfda336ac213efca3368a226efca3368a223efd23368a113eeda33689616efca33689216efd233686113dbda3362c213fed233605616ddda335ec813ddda335ec213deda335ad516deda335ad316deda335ac526deda335ac523deda335ac213dfca3356d212df5a3356c213ffc23354a112dfca334ac812dfca334ac512ffc233486112dfd23346c521cfda332ad812cfda332ad712d7da3326d513fdca331ed522cfea22aeda13cfea226ad812cfea226ad513cfea226ad512cfea226ad316cfea226ad213cfea226ac813cfea226ac513efe222686113fee222605616ddea225ec813deea225ad516deea225ad316dfca2256d313dfca224ec813ffc2224c6113d7ea2226d5138ff9bc215a128ff9bc20da128ff9bc14) else (if i<13 then 0x8869d732e9fa8869d712ebda8869d533ebea8869d522ebf28869d511eb7a88696553eb7a88696552ebda88696333ebda88696332ebea88696223ebea88696222ebf288696113ebf288696112eb7a88695512ebda8868e336ebea8868e226ebea8868a226ebea8868a223ebf28868a113ebda88689313ebf288686113d9fa885ec213dafa885ac523dafa885ac213fa7a88596556fada88596336faea88596226fada8858e336faea8858e226dbda8856d313dbea8856d212db7a8856c213fbca8854e223fbd28854e113fbe28854a112dbda884ec523fbd2884c6113dbea884ac532dbea884ac512dbea884ac312fbe288486112dbf28846c531dbf28846c521dbf28846c321cbfa882ad732cbfa882ad712cbfa882ad652cbfa882ad632cbfa882ad532d3fa8826d513f9ea881ed522cdfa77aeda53cdfa77aeda52cdfa77aeda36cdfa77aeda23cdfa77aeda13fc7a7799a553fcda7799a333fcea7799a223fcf27799a113ecfa77999a53ecfa77999a23ecfa77999a13fcda77999533fcea77999522fcf277999511fcda77999313fcea77999212fd5a77956333fd6a77956223fd7277956113ed7a77955a36ed7a77955a26ed7a77955a23ed7a77955a13fc7a77955636fc7a77955616fd5a77955313fd6a77955212fdca778ce223fdd2778ce113edda778cda26edda778cda23edda778cda13fcda778cd616fdca778cd522fdd2778cd511fdca778cd212fde27788a113edea77889a13fcea77889616fde277889511fdca77889313cdfa776ad853cdfa776ad852cdfa776ad851cdfa776ad836cdfa776ad826cdfa776ad823cdfa776ad812cdfa776ad513cdfa776ad512cdfa776ad316cdfa776ad213cdfa776ac813edda77696333edea77696223edf277696113ed7a77695516ed7a77695512edda7768e336edea7768e226edf27768e116edda7768d316edf27768a113ecfa77689616edda77689313edea77689216edf277686113fc7a77615656fcda7760d636fcf277605616dcfa775ad516dcfa775ad316fcda77596336fcea77596226fcf277596116fcda7758e336fcea7758e226fcf27758e116fcda7758d316ddda7756d313ddea7756d212fdca7754e223fdd27754e113fde27754a112ddda774ec813fdd2774c6113ddea774ac832ddea774ac812ddea774ac312fde277486112ddf27746c831d5fa7726d513cefa66aeda53cefa66aeda23cefa66aeda13fe5a66956333fe6a66956223fe7266956113ee7a66955a23ee7a66955a13fe5a66955533fe6a66955522fe7266955511fe5a66955313fe6a66955212feca668ce223fed2668ce113eeda668cda23eeda668cda13feca668cd522fed2668cd511feca668cd212fee26688a113eeea66889a13fee266889511feca66889313cefa666ad853cefa666ad852cefa666ad851 else 0xda52dde87b46d522cef86c6ad813eef06c6a1511cef86baeda81cef86b4eda81af785c5eda83af785c5eda82af785c5eda81cff03b06da26afe82c5eda13bfc82c5ed313aff01c699a52aff01c699a32bfe01c699522aff01c5ada82aff01c5ada52aff01c5ada238ffacc6ac8528ffacc6ac8328ffacc6ac8318ffacc6ac532adfacc6a2773aefacc6a2663aefacc6a2661af7acc6a2553afdacc6a2333afeacc6a2223aff2cc6a2113aff2cc6a2111aefacc69e663afdacc69e333aff2cc69e113afdacc696333afeacc696223afeacc696222aff2cc696113afdacc68e336afeacc68e226aff2cc68a1139bfacc62c2139dfacc5ec8139efacc5ac5239f7acc56c2139fdacc4ec8539fdacc4ec5139fdacc4ec2139feacc4ac8539ff2cc46c853abfacc2ae882cfdaaaaed533cfeaaaaed522cfdaaaaed313cbfaaa62c213cdfaaa5ec853cdfaaa5ec852cdfaaa5ec832cdfaaa5ec831cdfaaa5ec813cdfaaa5ec213cefaaa5ac853cefaaa5ac852cefaaa5ac832cefaaa5ac831cefaaa5ac523cefaaa5ac213cf7aaa56c832cf7aaa56c831cf7aaa56c213cfbaaa52c852cfbaaa52c832cfbaaa52c831cfdaaa4ec853cfdaaa4ec852cfdaaa4ec213cfeaaa4ac853cfeaaa4ac852cfeaaa4ac832cfeaaa4ac831cff2aa46c853cff2aa46c852cff2aa46c832cff2aa46c831e3faaa26e883c7faaa26e883e7daaa26e332e7eaaa26e223c7faaa26e223c7faaa26d513cbfa88aeda73cbfa88aeda53cbfa88aeda23cbfa88aeda13f8fa889de663f97a889de553f9da889de333f9ea889de223f9f2889de113e9fa889dda53e9fa889dda36e9fa889dda26e9fa889dda23e9fa889dda13f8fa889dd656f8fa889dd636f8fa889dd616f9da889dd533f9ea889dd522f9f2889dd511f9da889dd313f9ea889dd212fa7a8899a553fada8899a333faea8899a223faf28899a113eafa88999a53eafa88999a52eafa88999a23eafa88999a13fada88999533faea88999522faf288999511fada88999313faea88999212fb5a88956333fb6a88956223fb7288956113eb7a88955a36eb7a88955a26eb7a88955a23eb7a88955a13fa7a88955636fa7a88955616fb5a88955533fb6a88955522fb7288955511fb5a88955313fb6a88955212fbca888ce223fbd2888ce113ebda888cda26ebda888cda23ebda888cda13fada888cd616fbca888cd522fbd2888cd511fbca888cd212fbe28888a113ebea88889a13faea88889616fbe288889511fbca88889313cbfa886ad872cbfa886ad853cbfa886ad852cbfa886ad851cbfa886ad823cbfa886ad812cbfa886ad753cbfa886ad723cbfa886ad513cbfa886ad512cbfa886ad213cbfa886ac523cbfa886ac513cbfa886ac213eafa8869e663eb7a8869e553ebda8869e333ebea8869e223ebf28869e113e9fa)))) else (if i<21 then (if i<17 then (if i<15 then 0xbde97c20d522bdf17c20d511bde97c20d212bcf97c0c9616bdf17c0c9511bdd97c0ad313cef97b1ada81ff497354d522aef96caeda819ef96caed813de796c56c326bed96c54e336bee96c54e226def16c46c326aef96c295a32bee96c28d522bef16c285812bed96c22d533aef96c215a23aef96c215a13bed96c215313bee96c215212bee96c20d522bef16c20d511bee96c20d212aef96c149a13bed96c149313bef16c0c9511bed96c0ad533bed96c0ad313ee7965955a26eed9658cda26eee96568a226daf96562c326dcf9655ec326fe71655c5516fe7165589511de796556c326deb96552c326def16546c326eed9638cda26eee96368a226ffc1634c52129fd95c4ec8139fd95c4ec2139fe95c4ac8129fe95c4ac3128ff95c2ae3328ff95c2ae1128ff95c2ad8728ff95c2ad7328ff95c2ad712bf695c28d522bf695c20d522bf715c20d511bf695c20d212bf595c0ed823be795c0c9616bf715c0c9511bf595c0ad313cfd9536ac823cfd9536ac813cfd9536ac213df595362d523dbd95362c213ddd9535ec813ddd9535ec213ded9535ac213df595356c213fd59531ed523cfe9526ac812dbe95262ca12dde9525eca12dde9525ec812ff61525c5512dee9525aca12df695256ca12dfa95252ca12dfa95252c812dfc9524eca12cfe9522ad312afb94caa9813afb94caa9523afb94caa8813afb94caa8523bfa94c215212bfa94c20d522bfb14c20d511bfa94c20d212beb94c149616beb94c0c9616bfb14c0c9511df593c56c213dfd13c46c8538ff93c2ae5528ff93c2ae1128ff93c2ad712bfe13c285212bfc93c216223bfd13c216113bfc93c215212bfc93c16e223afd93c149a13bbd93c06e883dfd13162d2139fe92caed732df692c56ca12df692c56c832dfe12c46c852dfe12c46c832bfc92c22d533afe92c215a13afe92c215a12bfc92c215313afe92c20da12bfe12c20d511df711c56c831df711c56c321bfd11c22d533aff11c215a23aff11c215a12bfd11c215313bfe11c215212aff11c20da12bfe11c20d522bfe11c20d212aff11c14da12aff11c149a13bfd11c0ed823aff11c0c9a16bef11c0c96168ff8bcaaa8838ff8bcaaa8818ff8bcaaa5538ff8bcaaa5528ff8bcaaa2238ff8bcaaa1138ff8bcaa98738ff8bcaa98238ff8bcaa98218ff8bcaa95318ff8bc6a16328ff8bc6a16318ff8bc6a1536cfd8bc6a15338ff8bc6a1532cff0bc6a15118ff8bc6a1312cf78bc695512cfd8bc6893138ff8bc61da529ef8bc6156369ef8bc5958368ff8bc54da26b3f89ca21813c7f89c6ad51397f89c62d51397f89c5ed51397f89c5ad513a7f89c56da1397f89c56d31397f89c56d213a7f89c46da53abf88c5ada53bbd88c5ad533cdf87c6ad523ed787c695512dde87c56d212cdf87baeda52cdf87b5ada52cdf87b4e else (if i<16 then 0x552ad312cfda336ad813cfda336ad713cfda336ad526cfda336ad523cfda336ad326cfea226ad813dfca224ec5138ff9bc6a15338ff9bc6a15228ff9bc6a15118ff9bc6a13238ff9bc6a12128ff9bc6953138ff9bc6952128ff9bc6852139fd9bc5453139fe9bc5452128ff9bc215a238ff9bc215a139fd9bc2153139fe9bc2152129fe9bc20d5229ff1bc20d5119fe9bc20d2128ff9bc209a139fe9bc14d2128ff9bc149a139fd9bc1493139ff1bc0c95118ff9acaed8738ff9acaed8238ff9acaed8218ff9acaed5318ff9ac62c5318ff9ac62c5238ff9ac62c5218ff9ac62c513cbf9ac62c3218ff9ac62c321cbf9ac62c2138ff9ac62c213aef9ac61e663aef9ac61e661afd9ac61e333afd9ac61e331aff1ac61e113aff1ac61e111aff1ac606113aff1ac5c6113cf79ac56c8328ff9ac56c8328ff9ac56c8238ff9ac56c8138ff9ac56c8128ff9ac56c312cf79ac56c2138ff9ac56c213afd9ac54e336afe9ac54e226afe9ac54a226afe9ac54a223aff1ac54a113cfd9ac4ec852cfd9ac4ec851afe9ac4ca226cfe9ac4ac8538ff9ac4ac8138ff9ac4ac513cff1ac46c853c7f9ac26d513afd9ac215313afe9ac215212afe9ac20d522aff1ac20d511afe9ac20d212aff1ac209511afd9ac209313afd9ac149313aff1ac0c9511cdf9ab1ed526cdf9ab1ed523cef9ab1ad813cbf9a862c532cbf9a862c523cbf9a862c521cbf9a862c512cbf9a862c326cbf9a862c312ef59a8615533ebf1a8605512cdf9a85ec321cdf9a85ec213cef9a85ac523cef9a85ac521cef9a85ac321cef9a85ac213cf79a856c321cf79a856c213ef59a854d523ef71a8549511cfb9a852c521cfb9a852c321cfd9a84ec523cfe9a84ac532cfe9a84ac512cfe9a84ac312cff1a846c521ede9a81ed522eaf9a81ad812cff1a806da62ef71a7595511ef69a7549512cfe9a74ac832cff1a746c831cdf9a65eca32cfb9a652ca52cbf9a562ca12cbf9a562c213ef71a5605512cdf9a55eca32cdf9a55eca12cdf9a55ec832cdf9a55ec813cdf9a55ec812cdf9a55ec213ef71a55c5516cef9a55aca32cef9a55aca12cef9a55ac832cef9a55ac213cf79a556c831cf79a556c813cf79a556c812cf79a556c326cf79a556c321cfb9a552ca12cfb9a552c832cfb9a552c812cfd9a54eca12cfd9a54ec813cfe9a54ac812cff1a546c832cff1a546c831cff1a546c321efe1a5285212c7f9a526d513cbf9a362ca12cdf9a35eca12cef9a35aca12cf79a356ca12efd1a2605313cdf9a25ec813cfd9a24ec813efd1a24c5213cfe9a24ac813c7f9a126d513baf98c0c9616bbf18c0c9511bbd98c0ad313dde98b1ed522adf97caeda529df97caed523bde97caed522bf697c54d522bdd97c22d533bdd97c22d313adf97c215a23adf97c215a13bdd97c215313bde97c215212 else 0xa7d0a780a730a6e0a690a640a5f0a5a0a550a500a4b0a460a410a3c0a370a320a2d0a280a230a1e0a190a140a0f0a0a0a050a0009fb09f609f109ec09e709e209dd09d809d309ce09c909c409bf09ba09b509b009ab09a609a1099c09970992098d09880983097e09790974096f096a09650960095b09560951094c09470942093d09380933092e09290924091f091a09150910090b0906090108fc08f708f208ed08e808e308de08d908d408cf08ca08c508c008bb08b608b108ac08a708a2089d08980893088e08890884087f087a08750870086b08660861085c08570852084d08480843083e08390834082f082a08250820081b08160811080c0807080207fd07f807f307ee07e907e407df07da07d507d007cb07c607c107bc07b707b207ad07a807a3079e07990794078f078a07850780077b07760771076c07670762075d07580753074e07490744073f073a07350730072b07260721071c07170712070d0708070306fe06f906f406ef06ea06e506e006db06d606d106cc06c706c206bd06b806b306ae06a906a4069f069a06950690068b0686068106040587050a0499043403cf0376032902dc028f0242020101c0017f013e010900d4009f006a0035000097facc26d513cbfa882ad512cefa662ad512fde1a75c5212ffc1a34c52128ff8bc6893169fd8bc6093139fd8bc54d8238ffacc6ad8138ffacc6ad523cfda332ad5128ff9bc6a13138ff9bc6953238ff9ac62d5238ff9ac62d5138ff9ac62d5128ff9ac62d2138ff9ac56d213cbf9a862c321cbf9a862c213ebf1a8605516ebf1a8605316cfd9a84ec513cfd9a84ec213cff1a846c531cff1a846c321ef69a754d522cf79a556c832cf79a556c312cf79a556c213cfd9a54ec213cfe9a54ac832efe1a25c5216cfd9a24ec513efe1a24c5216cff1812ad512cff1812ad312bfe17c4c5212bde97c28d522fed1634c5216fd69531ed522afb94caa8853afb94caa8213bf994c0ed8239fd93caed823afd93c215a23afd93c215a13ffc1324c5212afe92c215a23aff11caa9812aff11c215a139fe8bc5cd522dde87b0ed5228ffacc6ad8538ffacc6ad8528ffacc6ad8518ffacc6ad8238ffacc6ad8128ffacc6ad5138ffacc6ad5128ffacc6ad2138ffacc6ac8538ffacc6ac8238ffacc6ac8138ffacc6ac5238ffacc6ac5138ffacc6ac213cbfa886ad873cbfa886ad871cbfa886ad813cbfa886ad713cbfa886ad523dbda884ec513dbda884ec213cbfa882ad312cdfa776ad813cdfa776ad536cdfa776ad526cdfa776ad523cdfa776ad326dcfa775ad536ecfa77595a26ecfa7758da26cefa666ad813cefa666ad713cefa666ad523cefa662ad312cf7a556ad813cf7a556ad536cf7a556ad526cf7a556ad523cf7a556ad326de7a555ad536ee7a5558da26df5a554ec213cf7a)) else (if i<19 then (if i<18 then 0x147d14781473146e14691464145f145a14551450144b14461441143c14371432142d14281423141e14191414140f140a1405140013fb13f613f113ec13e713e213dd13d813d313ce13c913c413bf13ba13b513b013ab13a613a1139c13971392138d13881383137e13791374136f136a13651360135b13561351134c13471342133d13381333132e13291324131f131a13151310130b1306130112fc12f712f212ed12e812e312de12d912d412cf12ca12c512c012bb12b612b112ac12a712a2129d12981293128e12891284127f127a12751270126b12661261125c12571252124d12481243123e12391234122f122a12251220121b12161211120c1207120211fd11f811f311ee11e911e411df11da11d511d011cb11c611c111bc11b711b211ad11a811a3119e11991194118f118a11851180117b11761171116c11671162115d11581153114e11491144113f113a11351130112b11261121111c11171112110d1108110310fe10f910f410ef10ea10e510e010db10d610d110cc10c710c210bd10b810b310ae10a910a4109f109a10951090108b10861081107c10771072106d10681063105e10591054104f104a10451040103b10361031102c10271022101d10181013100e100910040fff0ffa0ff50ff00feb0fe60fe10fdc0fd70fd20fcd0fc80fc30fbe0fb90fb40faf0faa0fa50fa00f9b0f960f910f8c0f870f820f7d0f780f730f6e0f690f640f5f0f5a0f550f500f4b0f460f410f3c0f370f320f2d0f280f230f1e0f190f140f0f0f0a0f050f000efb0ef60ef10eec0ee70ee20edd0ed80ed30ece0ec90ec40ebf0eba0eb50eb00eab0ea60ea10e9c0e970e920e8d0e880e830e7e0e790e740e6f0e6a0e650e600e5b0e560e510e4c0e470e420e3d0e380e330e2e0e290e240e1f0e1a0e150e100e0b0e060e010dfc0df70df20ded0de80de30dde0dd90dd40dcf0dca0dc50dc00dbb0db60db10dac0da70da20d9d0d980d930d8e0d890d840d7f0d7a0d750d700d6b0d660d610d5c0d570d520d4d0d480d430d3e0d390d340d2f0d2a0d250d200d1b0d160d110d0c0d070d020cfd0cf80cf30cee0ce90ce40cdf0cda0cd50cd00ccb0cc60cc10cbc0cb70cb20cad0ca80ca30c9e0c990c940c8f0c8a0c850c800c7b0c760c710c6c0c670c620c5d0c580c530c4e0c490c440c3f0c3a0c350c300c2b0c260c210c1c0c170c120c0d0c080c030bfe0bf90bf40bef0bea0be50be00bdb0bd60bd10bcc0bc70bc20bbd0bb80bb30bae0ba90ba40b9f0b9a0b950b900b8b0b860b810b7c0b770b720b6d0b680b630b5e0b590b540b4f0b4a0b450b400b3b0b360b310b2c0b270b220b1d0b180b130b0e0b090b040aff0afa0af50af00aeb0ae60ae10adc0ad70ad20acd0ac80ac30abe0ab90ab40aaf0aaa0aa50aa00a9b0a960a910a8c0a870a82 else 0x2279226822572246223522242213220221f121e021cf21be21ad219c218b217a216921582147213621252114210320f220e120d020bf20ae209d208c207b206a2059204820372026201520041ff31fe21fd11fc01faf1f9e1f8d1f7c1f6b1f5a1f491f381f271f161f051ef41ee31ed21ec11eb01e9f1e8e1e7d1e6c1e5b1e4a1e391e281e171e061df51de41dd31dc21db11da01d8f1d7e1d6d1d5c1d4b1d3a1d291d181d071cf61ce51cd41ccf1cca1cc51cc01cbb1cb61cb11cac1ca71ca21c9d1c981c931c8e1c891c841c7f1c7a1c751c701c6b1c661c611c5c1c571c521c4d1c481c431c3e1c391c341c2f1c2a1c251c201c1b1c161c111c0c1c071c021bfd1bf81bf31bee1be91be41bdf1bda1bd51bd01bcb1bc61bc11bbc1bb71bb21bad1ba81ba31b9e1b991b941b8f1b8a1b851b801b7b1b761b711b6c1b671b621b5d1b581b531b4e1b491b441b3f1b3a1b351b301b2b1b261b211b1c1b171b121b0d1b081b031afe1af91af41aef1aea1ae51ae01adb1ad61ad11acc1ac71ac21abd1ab81ab31aae1aa91aa41a9f1a9a1a951a901a8b1a861a811a7c1a771a721a6d1a681a631a5e1a591a541a4f1a4a1a451a401a3b1a361a311a2c1a271a221a1d1a181a131a0e1a091a0419ff19fa19f519f019eb19e619e119dc19d719d219cd19c819c319be19b919b419af19aa19a519a0199b19961991198c19871982197d19781973196e19691964195f195a19551950194b19461941193c19371932192d19281923191e19191914190f190a1905190018fb18f618f118ec18e718e218dd18d818d318ce18c918c418bf18ba18b518b018ab18a618a1189c18971892188d18881883187e18791874186f186a18651860185b18561851184c18471842183d18381833182e18291824181f181a18151810180b1806180117fc17f717f217ed17e817e317de17d917d417cf17ca17c517c017bb17b617b117ac17a717a2179d17981793178e17891784177f177a17751770176b17661761175c17571752174d17481743173e17391734172f172a17251720171b17161711170c1707170216fd16f816f316ee16e916e416df16da16d516d016cb16c616c116bc16b716b216ad16a816a3169e16991694168f168a16851680167b16761671166c16671662165d16581653164e16491644163f163a16351630162b16261621161c16171612160d1608160315fe15f915f415ef15ea15e515e015db15d615d115cc15c715c215bd15b815b315ae15a915a4159f159a15951590158b15861581157c15771572156d15681563155e15591554154f154a15451540153b15361531152c15271522151d15181513150e1509150414ff14fa14f514f014eb14e614e114dc14d714d214cd14c814c314be14b914b414af14aa14a514a0149b14961491148c14871482) else (if i<20 then 0x4479446844574446443544244413440243f143e043cf43be43ad439c438b437a436943584347433643254314430342f242e142d042bf42ae429d428c427b426a42594248423742264215420441f341e241d141c041af419e418d417c416b415a4149413841274116410540f440e340d240c140b0409f408e407d406c405b404a40394028401740063ff53fe43fd33fc23fb13fa03f8f3f7e3f6d3f5c3f4b3f3a3f293f183f073ef63ee53ed43ec33eb23ea13e903e7f3e6e3e5d3e4c3e3b3e2a3e193e083df73de63dd53dc43db33da23d913d803d6f3d5e3d4d3d3c3d2b3d1a3d093cf83ce73cd63cc53cb43ca33c923c813c703c5f3c4e3c3d3c2c3c1b3c0a3bf93be83bd73bc63bb53ba43b933b823b713b603b4f3b3e3b2d3b1c3b0b3afa3ae93ad83ac73ab63aa53a943a833a723a613a503a3f3a2e3a1d3a0c39fb39ea39d939c839b739a6399539843973396239513940392f391e390d38fc38eb38da38c938b838a73896388538743863385238413830381f380e37fd37ec37db37ca37b937a837973786377537643753374237313720370f36fe36ed36dc36cb36ba36a936983687367636653654364336323621361035ff35ee35dd35cc35bb35aa359935883577356635553544353335223511350034ef34de34cd34bc34ab349a34893478346734563445343434233412340133f033df33ce33bd33ac339b338a3379336833573346333533243313330232f132e032cf32be32ad329c328b327a326932583247323632253214320331f231e131d031bf31ae319d318c317b316a31593148313731263115310430f330e230d130c030af309e308d307c306b305a304930383027301630052ff42fe32fd22fc12fb02f9f2f8e2f7d2f6c2f5b2f4a2f392f282f172f062ef52ee42ed32ec22eb12ea02e8f2e7e2e6d2e5c2e4b2e3a2e292e182e072df62de52dd42dc32db22da12d902d7f2d6e2d5d2d4c2d3b2d2a2d192d082cf72ce62cd52cc42cb32ca22c912c802c6f2c5e2c4d2c3c2c2b2c1a2c092bf82be72bd62bc52bb42ba32b922b812b702b5f2b4e2b3d2b2c2b1b2b0a2af92ae82ad72ac62ab52aa42a932a822a712a602a4f2a3e2a2d2a1c2a0b29fa29e929d829c729b629a529942983297229612950293f292e291d290c28fb28ea28d928c828b728a6289528842873286228512840282f281e280d27fc27eb27da27c927b827a72796278527742763275227412730271f270e26fd26ec26db26ca26b926a826972686267526642653264226312620260f25fe25ed25dc25cb25ba25a925982587257625652554254325322521251024ff24ee24dd24cc24bb24aa249924882477246624552444243324222411240023ef23de23cd23bc23ab239a23892378236723562345233423232312230122f022df22ce22bd22ac229b228a else 0x6679666866576646663566246613660265f165e065cf65be65ad659c658b657a656965586547653665256514650364f264e164d064bf64ae649d648c647b646a64596448643764266415640463f363e263d163c063af639e638d637c636b635a6349633863276316630562f462e362d262c162b0629f628e627d626c625b624a623962286217620661f561e461d361c261b161a0618f617e616d615c614b613a61296118610760f660e560d460c360b260a16090607f606e605d604c603b602a601960085ff75fe65fd55fc45fb35fa25f915f805f6f5f5e5f4d5f3c5f2b5f1a5f095ef85ee75ed65ec55eb45ea35e925e815e705e5f5e4e5e3d5e2c5e1b5e0a5df95de85dd75dc65db55da45d935d825d715d605d4f5d3e5d2d5d1c5d0b5cfa5ce95cd85cc75cb65ca55c945c835c725c615c505c3f5c2e5c1d5c0c5bfb5bea5bd95bc85bb75ba65b955b845b735b625b515b405b2f5b1e5b0d5afc5aeb5ada5ac95ab85aa75a965a855a745a635a525a415a305a1f5a0e59fd59ec59db59ca59b959a859975986597559645953594259315920590f58fe58ed58dc58cb58ba58a958985887587658655854584358325821581057ff57ee57dd57cc57bb57aa579957885777576657555744573357225711570056ef56de56cd56bc56ab569a56895678566756565645563456235612560155f055df55ce55bd55ac559b558a5579556855575546553555245513550254f154e054cf54be54ad549c548b547a546954585447543654255414540353f253e153d053bf53ae539d538c537b536a53595348533753265315530452f352e252d152c052af529e528d527c526b525a5249523852275216520551f451e351d251c151b0519f518e517d516c515b514a513951285117510650f550e450d350c250b150a0508f507e506d505c504b503a5029501850074ff64fe54fd44fc34fb24fa14f904f7f4f6e4f5d4f4c4f3b4f2a4f194f084ef74ee64ed54ec44eb34ea24e914e804e6f4e5e4e4d4e3c4e2b4e1a4e094df84de74dd64dc54db44da34d924d814d704d5f4d4e4d3d4d2c4d1b4d0a4cf94ce84cd74cc64cb54ca44c934c824c714c604c4f4c3e4c2d4c1c4c0b4bfa4be94bd84bc74bb64ba54b944b834b724b614b504b3f4b2e4b1d4b0c4afb4aea4ad94ac84ab74aa64a954a844a734a624a514a404a2f4a1e4a0d49fc49eb49da49c949b849a74996498549744963495249414930491f490e48fd48ec48db48ca48b948a848974886487548644853484248314820480f47fe47ed47dc47cb47ba47a947984787477647654754474347324721471046ff46ee46dd46cc46bb46aa469946884677466646554644463346224611460045ef45de45cd45bc45ab459a45894578456745564545453445234512450144f044df44ce44bd44ac449b448a))) else (if i<24 then (if i<22 then 0x9c659c3c9c139bea9bc19b989b6f9b469b1d9af49acb9aa29a799a5c9a3f9a229a0599e899cb99ae999199749957993a991d990098e398c698a9988c986f98529835981897fb97de97c197a49787976a974d9730971396f696d996bc969f968296659648962b960e95f195d495b7959a957d956095439526950994ec94cf94b294959478945b943e9421940493e793ca93ad9390937393569339931c92ff92e292c592a8928b926e92519234921791fa91dd91c091a391869169914c912f911290f590d890bb909e908190649047902a900d8ff08fd38fb68f998f7c8f5f8f428f258f088eeb8ece8eb18e948e778e5a8e3d8e208e038de68dc98dac8d8f8d728d558d388d1b8cfe8ce18cc48ca78c8a8c6d8c508c338c168bf98bdc8bbf8ba28b858b688b4b8b2e8b118af48ad78aba8a9d8a808a638a468a298a0c89ef89d289b58998897b895e89418924890788ea88cd88b0889388768859883c881f880287e587c887ab878e877187548737871a86fd86e086c386a68689866c864f8632861585f885db85be85a185848567854a852d851084f384d684b9849c847f846284458428840b83ee83d183b48397837a835d83408323830682e982cc82af829282758258823b821e820181e481c781aa818d817081538136811980fc80df80c280a58088806b804e803180147ff77fda7fbd7fa07f837f667f497f2c7f0f7ef27ed57eb87e9b7e7e7e617e447e277e0a7ded7dd07db37d967d797d5c7d3f7d227d057ce87ccb7cae7c917c747c577c3a7c1d7c007be37bc67ba97b8c7b6f7b527b357b187afb7ade7ac17aa47a877a6a7a4d7a307a1379f679d979bc799f798279657948792b790e78f178d478b7789a787d786078437826780977ec77cf77b277957778775b773e7721770476e776ca76ad7690767376567639761c75ff75e275c575a8758b756e75517534751774fa74dd74c074a374867469744c742f741273f573d873bb739e738173647347732a730d72f072d372b67299727c725f72427225720871eb71ce71b171947177715a713d7120710370e670c970ac708f707270557038701b6ffe6fe16fc46fa76f8a6f6d6f506f336f166ef96edc6ebf6ea26e856e686e4b6e2e6e116df46dd76dba6d9d6d806d636d466d296d0c6cfb6cea6cd96cc86cb76ca66c956c846c736c626c516c406c2f6c1e6c0d6bfc6beb6bda6bc96bb86ba76b966b856b746b636b526b416b306b1f6b0e6afd6aec6adb6aca6ab96aa86a976a866a756a646a536a426a316a206a0f69fe69ed69dc69cb69ba69a969986987697669656954694369326921691068ff68ee68dd68cc68bb68aa689968886877686668556844683368226811680067ef67de67cd67bc67ab679a67896778676767566745673467236712670166f066df66ce66bd66ac669b668a else (if i<23 then 0x7c003e001f000f8007c003e001f000f8007c003e001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009407804602c319c1580dc09f01e00a04a04502309f099094e0ae04f80f00502501e01180b0c67056037027c07802812808c27c26425382b813e03c01209404613e132129c15f01e0080cc0b0023e0ae04b83f80f00402501184c84a7057c07801c2cc26f828e0fe03c00c078166137c15f01e00609f099e0a382f80f00304f9467057417c0780182e027f82be03c00a13632051dc15e00509419248ce0af00285c04a70574178017810e07c036009c08703e01b004e04381f00d8027021c0f806c013810e07c036009c08703e01b004a321a2eca2b7a282a24da218a1e3a1aea185a15ca133a10aa0e1a0b8a08fa066a03da0149feb9fc29f999f709f479f1e9ef59ecc9ea39e7a9e519e289dff9dd69dad9d849d5b9d329d099ce09cb79c8e else 0x6830a42852143e001f000f8007c003e001f000f8007c00210a1f000f8007c003e001f000b4085a042d0214850f8007c002d0214850a42842143e001f000f8007c003e001f00084a04a0825041f000f8004a0825041f000f8007c003e001f000f8007c003e001023088f84138209a104d0f8007c003e001f000f8007c003e001f000f8007c0025041282094107c003e001f000f8007c003e001782081307c003e001f000f8007c003e001f000f4087a043d021e810f8007c003e001f000f4087c003e001f000f80042c03e001f000f8007c003e001f000f8007c003d021e810f4087c003e001204090207a043e0012040f408481024081f000f40858102c0816040b02058102c0810440e42858102c0816040e4287c003e001f000f8007c003e001f000f800481024081f00094184a0c3e001f000f8007c003e001f000f8007c002f0616040f8007c003e001f000c0206010208610240f8007c003e001f000f8007c003e0018040c020601020741804081087c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c0025021281094084a043e001f000f8007c003e001f00081007c0024081204090204810240817810f8007c003e001f000f8007c00207a103d081f040f4207a103a081d07a0424081e810902048102408120409020481024081204090207c003e001f000f8007c003e001f00081c87c003d0212040f408481024081f00090204810240812040f8007c002f0412290f800427c245210b30914848a43e001f000f8007c003e001f000f8007c003e001f000f40878103d021f000f8007c003e001f000f8007c003d021f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c0021701f0009440421c3e001f000cc10481024081204090204810240812040902048102408120409020481020361020081004080204010200810040d420441022081104090204810200810040802040111b088d8445020441020081084080204810200810040882040102008100486c2040102008100408022281024088d8408422361024088d8446c223e102008100486420401024088a0408822281019088a044502040102008100408020401020081204090204010220811040802040102c0f40840e42040102008100408820421020081004080204810210810040802040102408110420021001080084004090208810240f8007c003e001f000f0207c003e001f000f800)) else (if i<26 then (if i<25 then 0x21439021c810e020701038081c040f408720438081c040e0206204213618820c4086214310218820c408426c310218810c4086a0435021a810c428621435021a810d4086214350218850c4286214350218820c4106208300818040d020681034081a040d0206810390a18040c020681034081a040c0206810300818040c020681030081e810c14860a430521e810f4087a0439021c810e020701038081c040e0207a043d021c810e408701038081c040f408720438081c040c408620c21281881084a06204310218810c418620431021a810d4186a0435061a810d4186a04350618850d4086a04310a10cc0c020601034081a040d0206010300818040c0206010310e10820f4087810305218290c1487a043d021c850e408720438081c040e02070103d021c810e0207010380818810c4286204310418810c4186204310218810c408620435021a810d4086214350a1a810d4086214310a18850d4087a04310418820f4087a04300818040c0207a0434081a040d0207214300818040d0206810340818040d0206010300818040d0206010300818850c4386214310e1e81084c042603d021c810e0207010310a18810c4106214310218810c4186204310218810c4086204310218810d4286a04350218850c4286a043d0218820f4087a04300818040c0207a043d0218040f4086810300818040d0206010310a18850f4087810305218820c408620c310218810c4086204350218820f4086010300818040c02068103d021f000f8007c003e001f000f8007c003e001f000f8007c003e001f00094404a2025101288094084a0c25041281094184a0825021283094104a0425061282094084a04250a1281094084a0825021281094084a043e001f000f8007c003e001f00094084a0c3e001f00094087c003e001f00094084a0825041281094084a0425021281094084a0425061281094084a0425021281094084a0425021281094284a0425021285094084a043e001f000b4085a042d0416810b4105a042d0416810b4105a042d0414880a44052202d0216810b4105a042d0416810b4105a042d0414850a4285220290e14880a44052202d0216810b4085a04290a14880a44052202d0216820b4085a082d0216820a4285214290e10880844042202d0216820b4085a08290a14850a44052202d0216820a4285214291010850f8007c003e001f000f8007c003e001f000f8004220251012880f800421c250e1f000f8004a2025101f00094407c003e001f000f8007c003e001f000f8007c00300816810b4085a042d0214870a4285220291014880b4085a042d0216810a4285214291014880b4087c00210e1287084287c003e0012880f8007c00251012880f8007c003e001f000f8007c002d0216830b4085a0c2d0216830b4085a0c2d0216830a42852142d021 else 0x4009e002004f00100278008013c004107e002083f001041f800820fc004107e002c04f0016027800b013c005809e002e04f0016027800b013c005c09e002088f00104478008223c00410fe002604f00130278009813c004c09e002604f001055f8008223c004c09e002604f001302780082cfc004c09e002604f00130278009813c004c09e0020b3f0016c17800b60fc004127e002093f0016027800b013c005809e002c04f0016027800b013c005809e002604f00130278008207c004103e002086f00170278008813a044409d022c04f0011027408821bc004409d022087f00100278009813c004c09e002604f0013027800b813c005903e002088f0016027800821fc005809e002604f0013027800b813c005903e002088f0016027800b013c00410fe002c04f0016027800821fc00410de002e04f0010437800b013c004127e002094f001049f800826fc004127e002093f001049f800824fc004127e002094f001043f800820bc004129e002e0af00104a7800826bc004137e0020b0f0017057800820fc004313e002189f00104a780090a08104040c142020e81108df4088453a044040c142020e811010740880818285c15e002e04f001705780082c3c005c09e00209bf0010587800ae07c005409e002e0af00104d78008253c005703e002e0af0015c1f800826bc004129e002e0af0017027800b60fc005b03e002c04f0015c1780082c3c005c15e002f000f8007c003e001229091484208245210980914848a421321229084c048a421301229084d848a421301229091487a043d021e810f4087a043d021e810f4087a04250418040c02060103e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f000f8007c003e001f0009438421c250c108608430421c305218290c14860a43d021e810f4087a043d021c810e408721439021c810e020701038081c040e020701038081c040f4087a043d021e810e408720c39021c810e020701038081c040e0207a043d021e810e408721439021c810e020701038081c040e020701038081e810f408721439021c810e020701038081c040f408720438081c040e0206220310218830c4106204310418810c4086204310618810c408620431021a810d4086a0435021a810c4386214311018880c4406a0435061a810d4186a0435061a810d418621435021a810d4286a04350218850d4087a043d021e810d020681034081a040d020601030081e810d0206810340818040d0206010300818040d0206010300818040c438621431101887084f87a043c0818290841860a4305218290f4087a043d021e810e408720439021c040e020701038081c040f4087a043d021c810e428720439021c040e020701038081e810f4087) else (if i<27 then 0x99085f00184f842f800c27c217c00604610de00304ac04f00181704cf800d21b813c006127809e003093c04f001f02340f800c013a07c006111903e003088c81f00181180bf800c223207c006113b05e003088c81f0018430027800e21a813c006127e00209bf00104a7800824fc004129e002093f00104df800824fc004127e002093f001049f800824fc004127e002093f0014444408a222208510510228868811441c408a013a045009d02209f88514414408a226204413710a209b8811442c408a626010511190a2887c85104a4408a21a2045107102288508214414408a226204510b10628838811442c408a626010510f90a2804e811059c428a20a204510d10228858831441c408a21620451051022804e811040f800820fc004105e002081f00104178008207c004107e002081f00100278008013c004103e002081f00100278008013c004009e002004f00100278008207c004009e002081f00100278008013c004103e002081f001040f800820bc004105e002081f00104178008207c004d05e002082f001340f8008207c0045105022094288114414088a20a0845105022288282114114088a18a044d07e002083f001040f8008207c004107e002083f001340f8008207c0045125022289281114294188a0ca0445065022681f001340f8008a14a044d03e002081f001040f8009a07c004040d022085f001042f8008223c004111e002085f00104478008217c00410be002088f001342f8009a07c004d03e002087f0010437800821bc00410be002086f001042f8008223c00408be002682f001340f8009a07c004135e0020aff001340f8009a0bc004d03e002088f00104478009a0bc004d05e002086f001043f8008217c00410be002086f00124478009217c004b05e002088f001059f800821fc00410fe00203cf00101e78009e0fc004d03e002085f0011c1f8008e0fc004139e002681f00105878009a07c00410be002783f0013c1f8009a0fc004d03e002087f001042f8008217c00410de002086f0013c1f8009a0fc004d07e002783f001042f8008217c004d07e002087f00104378009e0fc004040d022781f0013c0f8009e07c004f03e002085f001340f8008217c00410be002085f0010103408b013c005809e002e04f0013027800820fc005d03e002e04f0010437800b813c005c09e002c81f001640f800b013c005809e002c04f0016027800b013c005809e002c04f0017027800826bc004167e002082f001740f8009813c004712408238920413027800b607c005809e002582f0017027800b207c005903e002c04f0016027800b013c005809e002c04f001640f800b013c005809e002e04f00170278008223214491190a2288a85130278009813c004133e002815f00130278009813c004c09e002087c851143d4288267c0 else 0x10c0e408282801fa04d05213f10b008482988580408220118070c2f801008c05c617c00813212810be004029087004f0020148438027801025024fc006136127e0030988858041841040f800c20c207c006106103e003082081f0018418417800c208207c006106103e003086682f001842b40f800c114267c00613210be003085681f001842b40f800c21da0bc00610cd05e0030b3088f001843b41f800c215a0fc00610ad03e003085681f001843b41f800c2c0217c00610ad03e0030)))))
def lvlNew10:Packing:=(2826,5,7,0,0,16,0,dataNew10)
def hashNew10 (i:Nat):Nat:=(if i<4 then (if i<2 then (if i<1 then 0x180002548dcd7408faa4f9014e02342b07171fc66907294ae5c55fd2e8000000068860000148e000034e7491752bbe8f52a12c05c6a02396db3bbf0eaeaa880007ce4b197651c7ac33124e15580005d7992e0985a4cc751787b998000596834b911be8000224300006c8800001adc8c41b00732f5d3650d5c0000497f808b00002aea1d4ff4a2f4d485540827ea519a1a000062b6dc0373dd80005a91e1350d1f1b92bcaf007aad110519baf721c8fcb148cd617631408a063c984ae059cd4c5199d06512f98f848093b1800023aa80003b4e5cfa000075700000000000002b2aba365404a90040400004400700800001b010182e0f0c8043e2a0506402000013416000902c060805004d6061a8941a1d020001801028540605c90202400030d4ca3d080381003020402405050a8363b0308406090b81c36060907434020000c020014a8c104600014060f291404200000001c030a85c2c08030043a0f0800cca00000002e0700010000d2d81016101a1180400310002c23000243a03010880807008003e1902834002606024900505870a20c0003400040e0043e0a0f01406570d01460050101c90482b804200101024103920060180503804042a0c8000c1d1e8001609000341a100180844010300000060002c34222889402190a80c1c04170342e1e068440002002a8061e018cc00080201c060f0d000024804828040f020683c03040b8061a151ac0426018003615000005e1a0780c2a000080032000503868160b8080002029882202120600a0b02108200a008606e04128101220168b41010028002610000142802000000000010481c1e128080a11000240c200387406020980c02000000000090280400000403c020025000480a1481004030080c00150481060560180c10010c820080200808c6000781c2800038c0020000000c00c0300028000209c2402010287a01000802a0902034060102000fc02100d81407020184a290980c042400808600900048020c078541401098053403008083c000307436050380800180003c14270709806030301004751400452111604408010088400050080c0c0b000646600068580c01168603e001081c1a00000c4000001008380d0d0880407000001e0b188080a00000dc2a01028640a3e0480c3a000b8000017080d40e0400904001e040182202028081015008048004138105c09000001c0000068201d01820000000840000b068b0140301058081f02820120004800002305814001401804060b020a402000181402080004c1601038140802020204a010480806070800c1c0f0280016000180c1601000640c0a0002c00000e8200a2a028000a00000601a0f0083c04040280818000d81c04110280402070500000021200c2802008040e09020b834060000c0608008087a00158080006020003201 else 0xcf2a1e46de800fae474f27ab2011b7b73d9eeb80d5c8af9b8e0439a085bde3cadab898a934adf1bc37271f832800071ec816fcd70b2560000000043f780006b5c93bf800061375a4a00a9505741e2dbf71a67000070d0f20b2cfb12868c9483aa703d800002f9310ab55180000340b4ad752a304c89a792b3000004394a756becc02034098000118b3a47f2a080001bee800009c969a4ab24594300007c9448940000306539db62dad01c0000132b0000000011d72d4d39b7c3cbd4a3bb781080842053a2ecb40288000038ad0000000000000000642fcb945ab4d1958bce800079a5e3b789817cf4d0d180003929cccc4cde2bff23acad83ad7a032dc400229c02038bf86d3d3a5718c7f1691a010ad6dcc1080500002ba4800029bb000e6af67a7e000052d0e388527480000d0e7166554080001d67180b0440da7a000000005d078b18d454685fda1793840beb59a02121d090356f557410b1800000000cac5aec953d80001c4d25678b79a4c62864000031d1585390a9eb680000447c0000746f84e6e13c7ab79841b82693569ad835576bc2abc43b62445014e300004d769b9baa790000000039f9ac65c1c0997da2a609f8800000000973cd78b03855145aa300000000006852fc000050f3cc116502531bf3e0d3f42549432e835eb92f8b6ea4e63b83a9754b0c9a55239148a3c20a619a945d88be7d48036b60fe000022a438e480002335412534ca51fe00002556006f7d4bd214790e79b16bda128c247680000000517cb40fa833e023b39380006559ac8b60ecfcf5800059058000493b000000001c3b28b2b10a000033288000702a00001b638000000000000000407da8e9210111d200005bf9fc183c2800005d256a9261a9cc647d71c17100000000043c8000000050e674ea8000000061e56d58d082aa3efd21c44004293575da0469630000000033b0083b800003320000000004954d4a255e51568000296a4174c85564ffb3be62a00000000078cb3ca500007848fd530000708c1b4e827825204b7f000078817c2a8000000050b0781ae8c4e56eacc3eaff800021c81c74ebbd000000002b5785177a684d44f9b7147eb384ed15241c302bb45863730143c37d0219c3e5b30e000072d71010cbcf83f20000611380000d1fb4553074000000006b0bbd794a70039682bfc8042b15a51c92dc0cdd21ef8b426c6783b1000018c9a375fb2f80000546c0db4941800000000a3d631e603ee13c8000449b00000000206042d1807ea0fa391fba2993c8792363748d3f00003b048ade004680002aa54af680000000000000005b4d1d30b15b3157000000001b4ad35c488054d58cf6049f8000316e3998b1ac800000000000709f735bbaa700001370690f0355000000003d3a58bdb4080c268000185d8275800000004a22b38df2cb000010e) else (if i<3 then 0x3d43020d3a18e8dac9c50000000000004a39800052a380697a9d58d324488ae7156f80001149a4ee2bd93a866c5922a5ea8335716bf9429e00004581c21a8d2b80001939e95e5406c2b41484b091213e0000000014d648612b8ef9b438e9aa2ffc196ab5800000000000204000dd68c2fd2f31ae0179fd5e9a8d000034de8102800032d13c00db8f0000000061f124f1bd66348383448000000000000000000000000000000070b6a35f800000000000000000000000232f0000503103ab800040bb2931ba52c56b32fce094d3e55354319104e1e22cabb8cbdef1f059c722d7800004684938402cda166be8f3eb93397928fcedc8b164fd18b83cdc4c2ea86a8000118f0b09000042897d616d0e82e3a9e7000073d7f405800054255c0f50e2fc163a8780001b061b419b59e3a380000ccf80000834ebf145347c7500007a2bf8451c20b2dd000051dd89422bef3d16ea1300007187884aea2db4b0fb6480005d1d129dd35a6339e9cb43a7c9601a33e4f80000120760d5aa9b192c298c0000138358bf8b069044f84f349cc49009c4e2440d63000070e053ed8000000019ce32bb6b713243d9519281fb87287e0c52eaa92a0e3d00a2c4550a497229060b072bc8fa2c5909c434e354f84a7c8db9b03b9e88cfaa66447e18fd7bee6c1e956dc18d9d56aaac789a000024dcf1820c9159e44d7f543bc323c5271408eb60db51bb98b4d00977c178cb0070fdcd4cf544287180005487c99ef0f493383464f258237a800033260c7469ba9325f40600002c61e09d81c02314e390dce51b637a3fd2288000000029a1ac318ab710ab3231db37dc51331cdc3062e57d354d3af8851051aa37a0dc002ef03af8714d03b56839e9c0735216c8c31a4daa1ca36fcd43a3459381f86ea248eb1c1a0fc52ce266c83a0be305652a3ce1b900d77a248000388380000000000059b38561cccd2062abd9f81b80001018835273ed00005185ba6108f449cfb4d200002bade49580003197821f50a0098900000ce8000078c840ec0000240780001999a2997a90cd0101fc69165423b88880006cf700002cc40a73395c0000318a281919930000082b3c5613490310ec25c048546ec2d38a6321a34a38542b1944f11a407b0d06f54740a1c4f150d9f3fa800003d49c77b3c7f2b0fa8d80000c4849208000604d4960d1c61b9531c1c0d28d4aab561c2d58890163ecb54bbe840e80001ac900000c6bd5749b328cfa8000794778166c797093c468bd4600006a540000000009e0414f938e3a5d00000b8d0c8900004a96b38a14a094d55cc7800000000000000014f92ad98ba9cc4a2854b913301dbcfe091c92cc5ac1b235e3806482b08b951e0496e387f2a86cb3693200007811ed11ac0d2b35dca1f05d50b5fc12cd814c5a1a602b860cc4e41a947d28bc88a4347 else 0x131cdd36942455294c91d80004a9eac5f80002824800060abf83f5c16800062526c9bfb298000482c00001845dc3203485a27b145337a59ad92a11b36000048f3142f149d5996c92e926fcd290000016d000073e480005bdf4d7631df49f283922382b33078cc7cd11162a584800012224acfc10fc164208239a522eb33fb8bdb3c18eb16fd4c0d4249fa6d7b80002bc4fa4b335aec6f724d0000000000000000098a8000354000001c22f36400000439e43a58fbd1b0ccf36554eb07a87ce3b9e15480004947d361800034340000115a00001ba03d6d112ad122c9b9f4a4238100000d13d403800000000d3ed053487a793bd9730000039acb1103fa00001b9dc91490ef70d229903d696aa4bb7454763a05747100007a0c1d27a934e268acbcf343625eb45c800041467a46ab6c486fea98cb11c27280000959db1a3b028809b898dbe15524295d80006ad0598869d6941458596b8c84a21cef905b08169c9e9908ea4ead10d90bca44c8f1000019ea09b674b7131ebd641c7a42e9f12753dcd0fc7cd3e88814a58cf6e29544bee221725ad362823680003ca841e84c4b6ae1988494dbad5aa2f501e66352d3cc5ad2c895d8ff20030000000059118904f019e4b5800071129c817d0f2aefc8048a5f00007330d48be3b600002ce209db80006af88000750280002a11497291abf95f1a6980005aa9b8738000786d7bcd00001199000000007980e4fc80000000081a1367800000007b311cfc58c9409ef18739c780003564fd20b16b5abf448c509600000000000001da2aca08e11d517bb37c2d80006a9a00002ca62aba80aef3fd0000443629c1728f8000011b80007a5080001adb2bc980005021340a84abfb3350a59347ec6c333c000000006be20000143d918410969a507af1d1f514be2b6d78bc40c571d2934f528e3c0caa9aca59dc0c31aed8a7642674b000001c0e0c928000000000000cab000000000000414000006bd080000000215908116282000013d50000636000003909101e800058120000530ee98ebcba2a2e2a4000006300e06600007524800022b832998cc2e491800000ed540d80000000726432627a09712680001228411f7d33a80a6ad5bb8c7d0fd1ee4d82023931611c2c12aa023d8000392c8000317478e5800000000a1ecbba00000000130200006168800019ccbb660012b965ad05f1e580923106850702158000084faaeec55d7471800000003c3f2b2c000000000000644200002b37000000000000425cbd5780000000693d80000c6a62ced1d3bc8e800000004d521a06dce8a4e5800028875d6c80002a6cb19b083300002c59c97e9376fb50e03d1b79451072d4590b00005456800022328abcb18613b27d4eabf1d15ae110727b73daf39a72741375696c51795d6a01cad8a2fd335abe8000355bb8082a5a000)) else (if i<6 then (if i<5 then 0x259afc462000059d944a0521063c952c6a91ac19bdad630cc800078df0bd680003b2523bc0a4c5bffea82ab44027babca2b124d538000014e414d000028f24a9cc33b9114122464d090b95c3080004437c2314a8510b50000528b001fdc84225b800010a1139e586cc08a0054401404c96d6980007a6dfcd92caa3b77b8a6dba659c470990336aa812c60800023c212e6fc21cd41bb576c7f84a4da7603d47c7af4177283800079567c102cef0abc6cc0232d4a345a9741f3fc4daa6eb2b56135aa34a41499279097fb5810cd98f6d865cd3164bd00000000000060d55b2480001a3f71bd9066945702ef64a6c14100006ba9700c00004aeacd01c24e1cb28000587b81dae4496cd2a8dca0f0ad148aac8a125d0bbac5b859a2309c787d35dba47cf3b9ad7a9380006cf5549089a700007970431d800018d400000000025b000013c690bd41078b66dcb22ae8d95300002c9d80000000000000000ac76d5580d1030833a1c04b0000140b000004cb00007a3a01f75ceea1be00007541000068fe80000000799d9031911900007857800000000204cd5d80006c43e346eb22614a32e7848f435923bb7d504c4992ba4b65c8413334050cb06de54f348352b930522099c446b1f180006d7e5ab89262d948b3c62d19126ae82f800040013349a19480000ac488b9f3d5d56ab28a34f06bd22af7e265000001d5d25580001a8a8867bb1d000023891b4c59af484d88ac8aa25c8a00006d32000061bfe8e7aa6e21303ca9800000000000686b488780007a65e3f00000340a52000078484982e9051be13d4d03745b842ce4a970a664fe90e38d3c0000000000002d6011e1c291283ce2c16c7f000059d47b53156c547279fb0b9632faa118000053fcea0ed0472834000013fc000019f954d3785bcabe2962000033a70000298c800022c5183932ab73868000686a1d0d113a80006424a99a5bad54ac8b08c1d1eacd000063903902088df0288000000021de5a03151874b3f2f9d1b270ca7bd15c93ba4f198e637b897bb9806be680001475b30a8acabc85dc1cc0f700edb3bc8002db4ba53b9225e0e7620df8b8c8db99dc80001926009334472c990267fc29800002372c443cf2800000002b9193c5b1fd922769120000714b099ff46a84178000000012f411393489d95283c3e1ba34ed2a4ca86c7a5480004b3e2210a57dd8c60000297d7470518380000bae98af98cbe0de4c9672e11c5205057d088000724580006c66046cfa849ae61c79805602f1020b92cccd60e047e8d8518552c2f8f00000491eac090000353772ae4d04112924c680001817905880003085e8300c3aa9eb45300000255a751b24357969ad5c94ce03237ccabd7251c6d9fac4dd80003516441f2a1be9ef404c1d2f8498b4b680002ac80aa6aae28bb0bc430a8caa5e0b4cdb0b0b0 else 0xfabc0821700002a3e59e0884bc395a58373d88000000070ce9ce38000584283ea88dd80000000148ca9388000000054330000285f3c2e6bb4800043050000000000004cb8727d53e043e1e3ac632a1304000018f621ed00005534d30f832782c01c53ebf500000000414b8b403522d0c1000002f8789bf10ec49a80005110f82738250000292a235db223fbc70000601d4b5b0c10fc57895d654b000014b6594913f28d3e626480004a2f58357d7fc444b04400003115590d2964c31a815399116542818d5a14fc27c312a2413b3a7856dd7c93a0800019b800956d1aa24608b0b96b80001a20e8f28000297b2d001bce10dfcb8f9bfe824bdb3de8d3a9f0abb7008ee8adc4eb409b48e83930800049178000000012205cd6fcc58478dd65d582800029ebf1ce936e00004d73ec1d00000000048052f37c73b44ad1fec10060360923f1e300004463894d8d37eb1fba9f944e101e00005526dc533c35eb38957a947b0089ebe2f0e469c5945af550934500000000308f3b1931f80090bc19800068d8c48d42858b1b71a854bad4af9ada380ad2493840f8324933f37b1515a17c2801853ccc4f92d481dfd9cbeba5ea49800054c1bb4b0000506ba86720f865623c93422b53f30bbf0000000019dd00006c3d1280d80f92f3c4a72559350b6a5380001549dbe6749c23d3dd45b10cd02980001528800050a80000639caaf490068ad20afe582d2279921b053b087512e8093f43fb44372c0bb8b3da7f80005c3fdaeb94070000422ac190d03b042443b9123b2af080006368fa08810479e680000c54d19c2b3f648568791c1a000000002a7ad37edce42cb98000287c49f580004b037abdb8c7650480007aec0a694d23c1bf74bff83580000d770000000049f47acf4b948000119e32aedaf049618b438bd628c42ade80001497000000000000025934bb580bd40200003915ec212030ecb1f4aefbdc25780000617774cec07789bcd191b3825992f9550bd700000000313a01e9735f4b7c000022963c32ab2c80006499a85000b4850c40620470b981ccdb23cd9bb58481da6b1928596ae12f1c5f336a181b4b2080006c728a48795face0c322c51264462d392509d8aaf00ed01c90ea08b4403e7b3ad36c88b7008302aae580a1a200007925d46d5ab2e41bb02d8d62a87080000000000024e972dbaa01d2388d235d2e28a4c9ca3a1819378000433493a8322d78fcfd4520bbbb766be7a936d1087076c0f58000011d225fc8e200003bdfab1403e9014c9165156e000072c64c861064d868f4a11a77521e6385800070ba20d6f26bcc47eb88ab1844f7c23b809822d972268000609a98a782d342c8f90dd15ea1b6f0f8c4f899ab209f80004bc0588c80006b58fb9f7538bc4bc146dbb83157e98b8000000054e063b3c850b22ed34628b634da78b318c) else (if i<7 then 0xdf076034ff36f5bccd0bf198893f5da95800013ae3290457c196c8a11a298000014d18000000008a37a722b10000069bbb903003fcac7aa979ae24037930db1ff550ad326b55fb288f3f8e0918ba100002ad8bcf98cd891f600007121000033d1e0ff80002c730242000014c33061812e710c232b8c1b0319c133194f637e00001c15c12d5092e975ba70ed21414c00002824444580006b850000109e000000001c97ac50800013efb9cc000079dedd7ed30583f0f8788000000011f26b280000000000007bb5029f0000717e0000000002af8a353a0f000020de8c696881b35158228000392bd241eb42d33b7b72bbb68000000054889bd06945acdfb9d670cf01b4951dfd68e4df08fb637723e700006d52800000007170800008ebacc0d398000073099cb48000716f1c3ed2294a3adce99348800000002d8063d80000702f59e7ca7f0000337fe95c8d585cb8fc2880003a2a6be858e6d2b98000436981363b5e4bafcc1dc1b5d1aa942a580950eecd0672237cff351a11a098c5a92201bc29d980003b67253810c3b4b7abb2d13e800031a913b472af5a4ad19231b1d89c3cfb9303abc18d5b38494518e3e998ca8bf4f4ea4401897adceb9813583701f32b4a1d3180003905405c800000633b29707d5b21800001fbfa1dd31704676b97e0841836f2578a76f4c203a8d232544291a469018000008e0000026c7a1c41f6e0e8a56bb2ed79b30b6bed17aae4b53f8000000000007cfd8a4750d0281f68b7800008e54529f0f18000000034aa89e4e4600bdd22fb009ca2adeadddac2688680000000000014cf0807981500002b934d2251a281201413f27dd8c07046000002b162fa31cf00004008c2ad4b6ad34dc1505900bd7b11fcd3151879b986ec9e3b1663f600002c6100000d32e29bf361000073a369aa1d2c4a63aac0d4bde82aeccc92098000392450f9a4da81678a8f4c4c1b97557d7b9d74bc44c522fea2bd11c9800000000154705eb87262b3c207c9582462eb8ada802261b18308c18ce7bb7200000000090380003ac3e19842ed80003a02a458b1310a9280a0800078b238e3321f8a5d8000000041c368d78000696e8000000079f790ce747769bd0000243800005402f4f0b2a2dd2b12843b2e28bed9fd2d4e2a7c2063800050436c04487faab664ec71072b0d6acb8000602e04154a6a3b53b57561e2384e80003897030f5c5ea08ad2fdaad5101870a200000000719500006a874a4083d2aab1f4cde14428bacb7dc1a6fc9a0d25f39fe9938000325314bbc56680002399345b4436a3214d1358220b7c80007d3625638000000054e2d8aa2d0850023813a2dff9ac706e3874f8f7800011d8314efc11b45e01d350ae080f1a0580004afd00000000788d14d4511e6cc8828bc4314d1ed3e3e9d88a5c000d933cd219152d227788e else 0x2a008000312d941248a891a8800000003be471ed800000000055ea4280003bea7176ec6e3ace6b3d000032fb82ff00000000327e80002d478000000062266c3e00006d2acb20122180000000713fe573142bb230192b14e17c7d8a789075e423014853a24b80800052c9f1e889a6605100003d283af21b3ff3f683a569ea90038828623c641e083c6bcf3869b8c0b05a84698942faa7944e800003ec000000005cbf1c86c27cd1f48000000000007371c2154317d49f000063d363bdb370acd9c3c51bab00002c4c8bcb226d2a0cabcac3ba9c1ff1d0d47bd4c833130b1380002989e4920a89b966e99428d4dc017039e3a680000ca350ac3038d19669d5797a44a88000115bd46b6256ec3c2c82338b80000916f577800000005118c1e3d8104bdbb0c6916751c279c28000000050d671b55bfe5d368cecf34700007d8462e5c28ee2138000497f000001ec0000000028d94baf000059e12932804e30af000000000000035599a11258b11c226f7c5c41dc000002f2f0a53015c99d2378d9b2fa5100007c63145d00000000000000007555446519c3c27143506b27000020da00001d72f333ebf3f8c8b15099a3c1d7c821a487085e00005c4f7aee387060062c41000004cb8000609d00005294339b00001820c35d1182cae368fac919da25000011ff98170cd7c842236d80f90d4d982671346b415025d2cd94f44158b8ee548f80007b0a44d869d4fc22394af00ce00580002ca78000739c0000519f1cc9b55f49516c27000013c12d2da4457b01820aa87765264860bb3eed39d260a21d6d090000000000000000341300006b31a30c00000000605858eb5152138b050d882970e0d233731f2433aaabec053c38d19c9984fa73e852907f3bf)))
def lookupNew10:=lookupWord 707 3507 9 16 12 0 hashNew10
def dataNew11 (i:Nat):Nat:=(if i<18 then (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x42273fe6ad8739ff356c38cff9ab615a7fcd5b06d3fe6ad8269ff356c0b4ff9ab5d4e7fcd5aea33fe6ad7139ff356a9b4ff9ab549a7fcd5aa2d3fe6ad3269ff35698b4ff9ab485b77cd44cc7bbe6a2662dfb35119b6fd9a88ccf77cd3ccc7bf669e332dfe34f089efd9a58ccf7f4d2c44dfb660d636bdf2d65097ee965889bf78b2c22dfbc58e116bfb276291dfe92b204aff4958a657fa4ac312ffc2430896bf8aba20b7bc55caa5afea21a53d7f510d296bfa88688f5fd443425b7e9dda53dbf4eed28edfa7768db77d3334a5bbe999a51ddf4ccd11ef7a5568db7bd2ab447bde955a12dfb466d136fea22684ff75112c2d3fe6ad8539ff356c11cff9ab484f6fcd44ee7b7e6a2772dbf3513b8ef79a8954f7bcd44aa3bfa6a2223dfd351110eff1a8844f7ecd3c663b7e69d712dfb34b19b6ff1a5844b7f4d1c44dbfc68a113b7f3165095df97b284af7cb5aa6d7be5ad516bdf2d698b7ed9658cdbf3cb2aa2dfb658d316bef2b65095fd93b284afec9d9027ff44c6113dfb1571997fe0a1484b6fc3db4a5bbe1ada81dfe036d135ff2bb54477f5552425afea21a51d7f510d09edfa77684fe7d3bac6df3e9dd616fbd4eea917dea77484b77d3334a7bde955a13fcf4aab1b7e7a55585b7ed19b425fb68cd6169ff356c294ff9ab61467fcd5b0273fe6ad8129ff356a91cff9ab544e7fcd5aa25bde6a2552dfb3511996fd9a88cc77f8d44225afe6a1816ddf350b2b6ef9a858db6fcd3ae65bf6696332dfd34b111efe9a588877f8d2c227bfc684a12fdd2c711377e89b8886bfc4dc443ff80ae112bfe036d315fdabb54ceff55daa457f6aed313bfd5769097ef2665447f6d332627fba999212dfd34ea916fd9a58cc7fb4baaa45ff85c5212ddf2cad136ef963689bfb8a92a235fe26e332aff13708957f89b68dabfc4db045dbe26d636aff136a88d7f89b4c4fef43daa45fdc06e551dfd554a916ff2aa54477ed552627ef6a21533f7b510989fbea88484beed3baa67f7c9dd511ffc444a88ffca224c4f5fcd41505bf669d533dfe34ea88ef79a5545b7ecd1a62dbbe689616dfd34490b7f598554cffe8c0a627fdc595511ff92a7111ff5953548fff0a94225fda549512ffa262909ffe131484bfb452aa45cfe26e883aff137441f7d89b8ccbbf44dc4475fe26e223efe13708957f89b54cebfc4da623fd60ee553ffa077089ff682b954b7ed552a67efaa21522f7e510a88fdda774c4ff6d332a67fba999522feb4aa989ff6a55484bfe519aa45ff48cd511ff94669096f79a5294b7ecd19465ff454e113fed2a6a916fd9a854cf7f8d42a23bde695512dfb344989e7f89b68db5fcd43025bfa6a1522bfb2b6989dfe95b484bbf84daa239fe26da82cff136d09d7f89b58cfbec4daa67df626d313cff136d29e7f89b6946bfc4daa273ee52eaa3 else 0xfabb684b5fd555105afeaaa881ddf5553316f7aaa954f7ed554663ebea22661f6f5112ab7bda888cdbded444667efaa22226f7d5111117cfa77998be7d3bccc3f5e9de556faf4ef2a97dda778ccfef53bc44df7c9de116fcf4cd2a8feda668ccff6d334663fba99a221feb4ab199ff6a55888bfb92ac22dff28ce223ff94671117fd233845bfe919c227ff888a1169ff356c3b4ff9ab5d5a7fcd5ae6d3fe6ad7269ff356b8b4ff9ab208e7fcd590273fe6ac5329ff356291cff9ab144f7bcd3caad6fe62c326b7f316190dbf98b084eefcbd90a777e5ec852bbf2f64195df97b20c6efcbd902777e5ec326bbf2f6190ddf97b084ef7cb590a77be5ac852bdf2d6291def96b084efbcad864d7de56c321bef2b6109dfb94b214afdca58a4d7ee52c521bf72961935fb94b0c86fec9d90a57fa4ac853bfe236429dff11b214aff88d864d3fe2ae5529ff156c394ffabb6a0b7bd554aa5bf6aaa332f3f5113b97afa88998fd7d444cc5afea21a56d7f510d136bfa88685be7d3bccc7f5e9de553faf4ef2a8fdda778cdbeed3bc665f7a9de223fbd4ef110fdf277844bf79334227fbc99a112fed4ab1136f7a55685b7f511342dbfa889a12dfe35108b6f79a7954b7f8d3c223bde696556dfd3451136ff1a1844bf78c0ac2d7be5aca52bdf2d64195ef96b20c7f3cb2caad7de56c832bef2b6418dfb94b20cafdca590637f64ec513bfd256418dfe92b144aff88d90657fc46c531def1572ab6f78ab95477f455c44dbfa2ae221dfe1570895efabb595af7d5dac6de7ea22773f3f5113b8fbf288844fdf9444225afea21a72d7f510d1b7afa88595beed3bc663f7c9de113dbf4eed2b6dfa77694b6fd3bb44db7e9dda16fcf4cd2a9fe7a66954bf6d334665fba99a223feb4ab19b7f6a55888ffb52ac443ff28ce226dfb466d0b4ff9ab61ca7fcd5aea53fe6ad7239ff356b896bf9a8a20f5fcd45105afe6a2881dbf3513bb6ef9a899877bcd44aadbfa6a2226dfd3511116ff1a8844777cd3ccc5bbe69e661def34f2a9ef79a795477ecd3c66dbf669e333dfd34f111efe9a788877f8d3c225b7e69d716ddf34eb2b6f79a5954f7bcd2caa5bde696551dfd34b1116ff1a5845b7f8d2c223bf668e336dfe34708b6fe9a2888f7f8d1422dbfc686113fcf30ab2b5df97b28caf7cb59465fb658e336bf72965295fb94b284aff88d8a43afe2ae883d7f157440ef78ab954f7ec55c66dbf62ae331dfd157111eff0ab844fdbd444aa7edea22552f6f5112a8fbda888ccbded444663efaa22223f7d511110ebfa8869cf5fd4434e3ebea21636f5f510b0b6dfa77688f6fd3bb425f3e9dd656ddf4ccd09eefa66684bfad2ac665fd6956331fee4ab089ff7255844b7bd2ab44dfd6955533fed4aaa917f72555447fe519c443ff48ce112dfb466d11efda33684fff111) else (if i<3 then 0x31fdf4cc990fefa664c4bf7d330a63fde955a12fef4aac18ff7a556087fbd2aac25fde955536fef4aaa98ff7a554c9bfbd2aa643fde955312fef4aa90b7f7a5528cbfed19b425ff68cd821ffb466b937fda335c87fed19ae25ff68cd612ffb466a8b7fda334c9bfed19a643ff68cd216ffd444b097fea22545affcd5aea3bfe6ad516dff35690b7df9a89dcbfecd44665ffc6a2112dff350a996ff9a84c4bfecd2c663ffa696221fdf30f3317ef9879987fecc3c665ff661e331ffe30f088ff7986954bfbcc34aa3ff661a332ffb30d198ffe986888bff4c34443fde616552fef30b2a8ffd9858cc7ff4c2c445ffa616221ffe30b0897ff1858447fecc1c665ff660e331ffd3071117fe9838887ff8c1c225ffc60e111ffd305110fff1828447fecbb4665ff65da331ffb2eb19b7fd9758ccbfecbac663ffc5d6112ffe2eb088ffd9738cdbfecb9c663ffc5ce111ffe2e5088ff7965954bff4b2c445ffa58e222ffb2a719b7fd9538cc7ff4a9c44dffa54e222ffd2a7110fff153844bff8a9c223ffc546112ffd2651137fe9328887ff8994223efe2ae882dff156c3b6ff8ab61cf7fc55b0e3bfe2ad826dff156c10eff8ab54cb7fc55aa63fde22e552fef1172a8ffd88b8ccbfec45c663ffa22e221ffe1170896ff88b694bdfc2dd105efe16e881ffd0b71137fe85b8887ff82dc225bfe16da82ffd0a71137fe8538887dfc1dd103fde0ee551ffd0771137fe83b88877fc1db503fde0ae556ffb05719b6ff81b6a0bdfd442a65efea21512fdf4ccc297efa6660cbf7d332a65fbe999512fef4aac197f7a5558cbfbd2aaa65ff68cd512fef3512a97fd9858ccbfecb2c665ff658e332ffb2a71997f78a8954bfec5446657be5ac526bdf2d61935ff11b21467fcd5864d3fe5aeaa2bfb276429dfe92b214a7fc8dd5453fe2ad5129ff576d29cffabb68da7fd5db427efca22116fee4ab088ffe22284467fcd590a33fe6ac5369ff3562934ff9ab0c867fcc5d5457be5ac5369ff2b75514ff93baa8afec9d84277fc46c3219ff156c294ff8ab60ca7fc55ae253fe2ad6529ff576d39cffabb69c67fd5db4ad3feaeda519ff576d136bfaaaa20f6fd554ee7b7eaaa771ddf555331ef7aaa95477f5554447bfaaaa221dfe555089eff2aa844bcfd444eedefca22111d7f510d3b7df2778447f75334445ff48ce111ffc4450894ff9ab214e7fcd590a53fe6ac8329ff356418cff9ab20867fcd590253fe6ac5319ff356290cff9ab144a7fcd586253fe6ac213dfd34f1136ff1a7845aefcbd90a377e5ec812bdf2d6428def96b1486f7cb586437ee52c851bf72964095fd93b2146ff49590a37fa4ac832bfe236418cff8aba20a7fc55c6653fe2ae1129ff156c094ff8ab5cca7fc55ac653fe2ad5329ff1569894ffabb6a0e7fd5db5033feaeda529ff576d11cf else 0xc0a625bfe5eda82dff2f6d28ff7976954bfbcbb4aa3ff65da333ffd2ed110fff176844bf7cbb2c43ff65d9533ffd2eca917ff1765447fecbb2627ffa5d9212ffb2eb199ffe975889bff4bac443ffc5d6116ffe2eb089fef97558dbf7cbaac2dfde5d5526fef2eaa90ffd9754c4fff4baa425ffa5ce226ffd2e7110fff173845befcb9ae4df7e5cd721fdf2e6b0b7fd97354dbfecb9aa63ffc5cd511ffb2e69937fd9734c87ff8b9422dffc5ca113fdf2e4b0b7fe972549bff4b92a43ffc5c9511ffb2e4989fff171844fff8b8c225bfe5ada51fdf2d6a9b7f7965954ffbcb2caa3fbe596336ffb2cb199ffd9658cc7ff4b2c447ffa596221ffe2cb0897ef9655cdbf7cb2a64dff6595313ffb2c7198ffe9638887ff8b1c225fbe58d726ffd2c6a917ff1635447ff4b14447ffa58a221dff2b6d416ff95b6a06ffcada6257fe56c821bff2b64095ff95b0c4bff8a9c22dff654e113dff2a6d097fd9535c8ffeca9ae27ff654d623ffb2a6b09ff7953549bff4a9aa45fde54d521ffb2a6909ffe953484bff4a9444dffa54a221ffe2a5088ffe952584bff8a8c2277fe4ec821bff276290fff132845b7fc993425fbe4c9616ffe264a88fff131844b7fc95b5037fe4ac531ffe243089eff91b6a0b7fc8db4a5fde2ae552ffb1571996ff8ab61cb7fc55b047bfe2ad632dff156a9b6ff8a8694b7fc543465ffa2a1522ffb14b1997ff0a1604bbfc4db505dfe26d513dff1175516ff88b69c77fc45b447bfe22da13fbf0f6a937df87b54877fc2dd545efe16e883ffb0b719b7fd85b8ccbfec2dc663ffa16e223ffe0b7089eff85b6a1b7fc2db507bfe16da81dff0b6d11eff85b684ff7c2dac6dff616d313ffe0a708b7ff053844b7fc29b425ffc14a116dff0775517bf83ba20bfbc1dcaadfde0ee552ffe0770896ff83b6a1b7fc1db505bfe0eda76dff076d38eff83b695b7fc1db4a5bfe0eda26fdf076b2b7bf82ba207fbc15caa3ff60ae331dff056d436ff82b6a0f7fc15b503bfe0ada56dff056d29fbf81ba20fdfc0dd105fde06e553fef0372a97fe81b888f7fc0db507bfe06da53dff036d296ff81b688ffec0daa67fdea22552ffb5111997bfa886947dfd443425efea21872f7f510c38fbfa88614bdfd4430a3efea21832f7f510c18fbfa886087dfd442ea5efea21751f7f510b98fbfa885c87dfd442e25efea21652f7f510b197bfa8854c7dfd442643efea21312f7f5105297bfa8828cbdfd440a63f7e9dda51fbf4eec317dfa776187efd3bb0a5f7e9dd851fbf4eec197dfa7760c7efd3bb043f7e9dd652fbf4eeb197dfa77584befd3baa6df7e9dd532fbf4eea98fdfa77549befd3baa43f7e9dd516fbf4eea897dfa774c9befd3ba643f7e9dd216fdf4ccc28fefa6660c7f7d333043fbe999752fdf4ccba8fefa665cc7f7d332e43fbe9995)) else (if i<6 then (if i<5 then 0xfefa665c4ff7d332e25fbe999521fdf4cca89fefa66484ff7d3314a5fbe998a32fdf4cc2997fda558ccbfbd2ac665fde956331fef4ab1137f7a5568dbfbd2ab465fde955a31fef4aad10ff7a5560dbfbd2ab04dfde955812fef4aab9b7f7a555cc7fbd2aae4dfde955721fef4aab897efa5558dbfbd2aac63fde955623fef4aab10ff7a55584ffbd2aaa4dfde955521fef4aaa8b7f7a55544ffbd2aaa25fde955316ffb4aa989ff7a55484ffbd2a9425fde954821fef4aa4097f7a550c4bfed19c44dffa8ce221ffe467088ffda336887fed19b04dff68cd812ffb466b91ffda335c5bfed19ae27ff68cd623ffb466b10ffda33584ffed19aa4dff68cd521ffe466a88ffda334c4bfed19a427ff68cc821ffb4662937fda33144bff911422dffa889613ffd444a89ffea22544bff511262dffa889312ffd44490b7fea22484fff5110a27bfe6ad856dff356c29eff9ab614affcd5b0a5bfe6ad851bff356c28eff9ab60cb7fcd5b047bfe6ad821bff356c10eff9ab604affcd5b0257fe6ad752bff356b90dff9ab5c4affcd5ac25bfe6ad531bff356a98eff9ab5486ffcd5aa43bfe6ad513dff356a895ff9ab544b7fcd5a643bfe6ad316dff3569896ff9ab484effcd58a65efe6a2882fbf3513bb7ef9a8998bfbcd44aadff66a2336ffd3511136ff9a8889b7fcd430a5bfe6a1832dff350b196ff9a854db7fcd42a63bfe6a1512dff3509916ff9a8484b7fcd414a5bfe6a0a32dff3505097ef9a7998bfbcd3caadfde69e552fef34f2a8ffd9a78cdb7fcd3c66dff669e332ffb34f198eff9a78cc7ff4d3c44dffa69e221ffe34f0896ff9a7609bfbcd34aa5ff669a332ffe34d0897f79a5955bfecd2c66dbfe696336ffb34b1997fe9a5889b7fcd2c44dbfe695851dff34ac18eff9a5608f7fcd2b043bfe695531dff34a990eff9a54c4b7fcd2a623bfe695211dff34a5197fe9a3889b7fcd0aa25bfe685312dff316d295ff98b54caffcc5aa637fe62d321bff3162995ff98b14c6ffcc58a437fe62c512bff3161897ef987998ffbcc3caa5fde61e551ffb30f19b7fd9878ccfff4c3c443ffc61e113ffe30f0896ff987695bdfcc3b0adefe61d851f7f30ec137bf9876087efcc3aeadf7e61d751fbf30eb9b7df9875cc7fecc3a627ffa61d212fef30d2a9ffd9868ccfff4c34447ffc61a112ffb30ca99ffe986548bff8c32a23ff6619313ffd30c9097f7985955bfbcc2caa7ff6616336ffb30b199ffe985889bff4c2c447ffc616113dff30ad097f798554cbfbcc2aa63ff6615313ffd30a9097fd9838cdbff4c1c44dbfe60da12f7f306c137bf9836087fecc1aa65ff660d531ffd306a917ff1835447ff4c1a425ffa60a226dff304d09eff982684bff4c12c43ffa609526ffd304a90fff1825447ff4c1264dffa609321ffe3030897ff181544bff8 else 0xd326ffb2c69897fe963484bff8b14227ffc58a112dff2c4d097ef962584ffecb12627ffa589213dff2b6d09eff95b684affcada6437fe56d316ffb2b6989dff95b4c46ffcad95057fe56ca32bff2b64195ff95b20c6ffcad90477fe56c813bff2b6190eff953689b7fca9b447bfe54da16dff2a6d09ffd953608ffeca9b027fbe54d616ffb2a6411ffe952888fff8a9422dffc54a113dff2a4d097fe952604bf7ca92c2dfde549516fef2a4a89ffe952544bfeca92627ffa549312ffd2a45097fe952204bff4a90625ff6545313dff276d416ff93b6a077fc9db4a5bfe4eda51ffb276a89fff13b5446ffc9da42d7fe4eca82bff2765295ff93b2146ffc9d90257fe4ec526bff2762896ff932685b7fc993427ff64c9311ffe26290b6ff92b6947ff495aa257fe4ac536bff256289eff91b694ffec8daa677fe46c823bff2362995ff91b149affc8d8a47bfe2ad312ffd146a9177f89b698fbfc4db4a7dfe26da31eff136d09ff788b954fff445c447ffc22e113dff116d39eff88b694fff445aa45ffa216222ffd10b110fff085844b7fc42b425ffa215212ffd1071117fe8838887ff841c225ffc20e111dff106d097fe883548bff841aa23ffa20d212ffe105089fff0825447fec412627f7e1eda52fbf0f6a91fef86b604ff7c35b025bfe16da36dff0b6d137fe853888b7fc29b42dfbe14d616ffd0a69096ff852685bf7c292c2dffc0c9511f7f057441ff782b954fff815c227bfe0ada36dff056d09fef82b595bfec0dc665bfe06da73ffe036d315ffabb61c6ffd5db0437feaed632bff576a995ffabb54c6ffd5da625efeaaa882dff5554417efaaa998bfbd554aa5ff6aaa332dff554c39effaaa61c77fd553043bfeaa9532dff554a98fdfa889dcbefd444ee3efea22552fef5112a8fbfa888ccbfed444663efea22331f7f5111137fea88888bff5444443ffca22112ffe511088fbfa8869cbdfd4434e3bfea21a71f7f510d317bfa88694bdfd443465efea21a31f7f510d10fbfa8861cfdfd4430a7efea21762f7f510bb0fbfa885d5bdfd442ea7efea21736f7f510b997bfa885c9bdfd442e47efea21713f7f510b097bfa8854dbff5442a45efea21521f7f510a89fbfa884c9bdfd442427ffaa21212f7f5105097bfa8814dbdfd440a65efea20526f7f510290fbfa88144fdfd440a25efea20312fbf4ef198fdfa77698befd3bb4adf7e9dda52fbf4eed1b7dfa7768c7efd3bb443f7e9dda12fbf4eec31fdfa77615befd3bb0a7f7e9dd836fbf4eec137dfa77594fefd3baca3f7e9dd631fbf4eeb11fdfa775887efd3bac27f7e9dd523fbf4eea89fdfa774c5befd3ba625f7e9dd213fbf4ee1897efa66954bf7d334665fbe99a331fdf4ccd297efa6668cbf7d333425fbe999853fdf4ccc09fefa66604bf7d332ea7fbe999732fdf4ccb91) else (if i<7 then 0xfcd2c665bfe696331ffd34b111eff9a5888f7fcd2c443ffc696113dff34b089fff1a5844b7fcd2b443bfe695853dff34ac296ff9a560db7fcd2b067bfe695832dff34ac136ff9a5608b7fcd2b023bfe695726dff34ab90eff9a55c477fcd2aca3bfe695632dff34ab10eff9a554db7fcd2aa65bfe695521dff34aa8b6ff9a5544f7fcd2aa25bfe695326dff34a991eff9a54c8b7fcd2a62dbfe695313dff34a90b6ff9a5484f7fcd2a425bfe694a12dff34a418eff9a520877fcd28643bfe694312ffb34719b7fd9a38ccbfecd1c663bfe68e226ffd347110fff1a3844b7fcd1b04dffa68a226dff344a89eff9a24c4f7fcd1242dbfe689213dff344289eff9a1604b7fcd0ae25bfe685513dff342909eff98b69477fcc5b4257fe62d762bff316bb0dff98b5d4affcc5aea37fe62d731bff316b90dff98b594affcc5aca37fe62d632bff316b18dff98b5886ffcc5ac257fe62d521bff316a895ff98b4c4affcc594a57fe62ca32bff3165095ff98b144effcc58643fde61e556fef30f2a9ffe987889bff4c3c447ffc61e116dff30ed29eff987694b7fcc3b4a3bfe61da16dff30ed09fbf987614fdfcc3b0a5efe61d823fbf30ebb0fdf9875d4fefcc3aea5f7e61d713fbf30eb897df9875c47f7cc3acadfbe61d636fdf30eb0b7fd98754cfff4c3aa45ffc61a113dff30cd28eff986684bdfcc33027fbe619653fdf30cb297ef9865947f7cc32c65fbe619631dff30ad11eff985685b7fcc2b427fde615653fef30ab297f79855947f7cc2ac6dfbe615616fef30aa9b7fe985548bff8c2aa23bfe60da23dff306d0b6ff983684fdfcc1b045ff660d632ffb306b18fef983585bfecc1aa6dffc60a116ffe3050896ff982685bdfcc1302defe609813f7f304c08ffe982588ff7cc12c2dffa609523ffb304989fff181844fff8c0ac27ffc605513dff2f6d40eff97b694b7fcbdb4257fe5ed652bff2f6b28dff97b58c6ffcbdac437fe5ed612bff2f6a9b7fd97b54ceffcbdaa637fe5ed526bff2f6a90dff97b545affcbdaa257fe5ed511bff2f69935ff97b4c87fecbda6277fe5ed216fef2ed2a9ffe976888fff8bb4227bfe5d9a51dff2ecd097df9765c4fefcbb2e25fbe5d9653fdf2ecb297ef9765947f7cbb2c47ffa5d6223dff2ead0b6ff975684bfbcbaaa47ff65ce332ffe2e70896ff973685b7fcb9b425ff65cd532dff2e4d0b7df9725c4fefcb92e23ffa5c9523ffe2e2a89fff171544bfecb8a627ffc5c5213dff2d6d416ff96b6a077fcb5b4a5bfe5ada12ffb2d6a99fef96b545affcb5aa25ffc5ad511bff2d69915ff96b4c86ffcb5a6257fe5ac532fdf2cb1137ff165844ff7cb2b06dfbe595726fdf2cab11fef9655887ff4b2aa45fde595513fef2caa897ff1655447ff4b2a425fbe58e226ffd2c7111fef963609bf7cb1aa4dfbe58 else (if i<8 then 0x11fbfa88684f7fd443427bfea21a12f7f510c09fbfa885d8fdfd442e23efea21653f7f510b28fbfa8858cfdfd442c63efea21623f7f510b117bfa885887dfd442c27efea21526f7f510a91fbfa88545bff9442a23efea21311f7f51090b7bfa880c87efd3bc66df7e9de332fbf4eed31fdfa77694fefd3bb465f7e9dda26fbf4eed09fdfa77605befd3bb027f7e9dd812fbf4eeb19fdfa774c47efd3b9065f7e9dc831fbf4ee4097efa669547f7d334443fbe999a53fdf4cca91fefa661487f7d330643ff6956336fef4ab19b7fda558cc7ff52ac44dffa956222ffd4ab110ff7a558887ff92ac22dffc956112fef4ab0896ffa5568dbfbd2ab44dbfe955a23dff4aad0b7f7a55684f7fd2ab427bfe955a12fef4aac117f7a55605bfbd2ab027fde955732fef4aab91ff7a555c5bfbd2aae27fde955711fef4aab19ff7a55588bf7d2aac2dfde955523fef4aa988ffea55484bfbd2a9065fde954831fef4aa411ff7a550c9bfbd2a8643ffa8ce226ffd4671117fda338887ff919c22dffc8ce112ffb4670897fda33689b7fd19b42dbfe8cda12ffb466c11ffda33605bfed19b027ff68cd711ffb466b117efa33585bfed19aa47ff68cd513ffb46698b7fda33284bfed199047ff68cc812ffb466290ffda33144f7fd11342dffa889816ffd444c09ffea22604bff5112e2dffa889713ffd444b88fefa22585affcd5b0e57fe6ad871bff356c31dff9ab618b7fcd5b06d7fe6ad832dff356c18dff9ab60c77fcd5b04dbfe6ad813bff356bb1dff9ab5d8affcd5aea77fe6ad732bff356b98dff9ab594affcd5ac65bfe6ad536dff356a995ff9ab54cb7fcd5aa4dbfe6ad523bff356a89eff9ab4c9affcd5a6437fe6ad312bff3564295ff9ab20caffcd59063efe6a2881fbf3513b8eff9a8955b7fcd44aa5fde6a2551dff35119b6ff9a88ccbfecd44663bfe6a2331dff351111ffe9a8888bff4d44443bfe6a2221dff351089eff9a8844b7fcd43425bfe6a1872dff350c29eff9a861477fcd43063bfe6a1821f7f350c096ff9a8604b7fcd42ec5bfe6a1756dff350ba96ff9a85cdb7fcd42e65bfe6a1726dff350b896ff9a8594b7fcd42c63bfe6a1622dff350b096ff9a854cfff4d42a45bfe6a1522dff350a89eff9a854477fcd4264dbfe6a1323dff350990eff9a84c4f7fcd42623bfe6a1216dff350909ffe9a8484b7fcd42423bfe6a0536dff3502996ff9a814c77fcd40a4dbfe6a0513dff3502896ff9a80c4b7fcd3c227bfe69d862dff34ec30eff9a7614b7fcd3b0a3bfe69d836dff34ec196ff9a760c77fcd3b047bfe69d821dff34eb196ff9a758c77fcd3ac43bfe69d612dff34ea9b6ff9a754c77fcd3aa23bfe69d326dff34e990eff9a74c5b7fcd3a625bfe69d311dff34e4096ff9a70c4bfbcd34aa7ffa69a223dff34c5197f79a5954b7 else 0x62c526bff316291eff98768db7fcc3b447bfe61da12fbf30ebb1fdf9875d8befcc3ae67f7e61d732fbf30eb8b7ff18754477fcc334a7bfe619a52dff30cd11eff986684fdfcc33025fbe619633ffe30b08b6ff98568dbfecc2aa67ffc60e116f7f306c11ffe982888fff8c14227ffa609622ffd304991ffe982484bff8c0ac25ffc605516ffd3029096ff97b6a0f7fcbdb4a7bfe5eda13bff2f6b29dff97b58ceffcbdac657fe5ed623bff2f6b09dff97b54ceffcbdaa657fe5ed523ffd2f6a915ff97b544fff8bdaa237fe5ed311bff2f6909ffe97b484affcbda4237fe5ec831bff2f61896ff976694f7fcbb34a5bfe5d9a23dff2ecd09eff97568db7fcbab44dbfe5d5a23dff2ead09ffe973888fff8b9c227bfe5cda13fbf2e6b91ffe973548bff4b9a425bfe5c9a13fbf2e4b8b7ff171545bff8b8a42dffc5c5211dff2d6d41eff96b694f7fcb5b4477fe5ad532ffd2d6a915ff96b548affcb5aa437fe5ad513bff2d6991fef96b4c5bfecb5a6277fe5ad213ffd2d69095ff96b484affcb594a57fe5aca32bff2d6298eff965688f7fcb2b425fbe595826fdf2caa8b7ef965485bf7cb2864dffc58e113dff2c6d11eff963684f7fcb1b425fbe58d716fdf2c6b10fef963545bf7cb1a42dfbe58c526dff2c4d09fff16254477fcadb507bfe56da23bff2b69935ff95b4c8affcada42d7fe56d213bff2b6908dff95b284affcad864d7fe56c213ffb2a7111ffd953548ffbca9aa45ff654d513ffe2a6a88ffd953204ffeca98427ffa54a112dff2a4d0b7fe952684bff4a92e25ffc549511fef2a4a88ffe951484b7fc9db425ffa4ed522ffd2769095ff93b484affc9da423ffc4ca112ffb26498b7ff131484b7fc95b507bfe4ada53dff256d09ffd92b54cfff895aa23ff64ad313bff256409eff91b6a0f7fc8db4477fe46c853bff23629b6ff8a568cbfec42c665ff6216331ffb10a989eff882684f7fc29b44dffc14a113ffb0a4989ffd83b608fff41daa45ffc0ca116dff064d0b7ef832585bf7c15ac6dffa06d522dff576d415ffabb6a0affd5db4a57feaed876bff576c39dffabb61caffd5db0ad7feaed852bff576c28dffabb60daffd5db0657feaed831bff576c135ffabb608effd5dae6d7feaed731bff576b295ffabb58c6ffd5daa4d7feaed521bff5769935ffabb4c86ffd5da42dbfeaaa881dff5552a96ffaaa8ccb7fd554663bfeaa9a82dff554c31effaaa618b7fd5530a7bfeaa9852dff554c28effaaa60cb7fd553063bfeaa9763dff554ba9effaaa5d477fd552e63bfeaa9723dff554b90effaaa5c4f7fd552ca7bfeaa9632dff554b11effaaa584f7fd552a27bfeaa9321dff554909effaaa144fdfd444aadefea22551f7f51119b7bfa888887dfd444225bfea21a73dff510d397bfa88698f7fd4434a5bfea21a51dff510d)))) else (if i<13 then (if i<11 then (if i<10 then 0xbfed442627efea21211f7f510291fbfa880c9befd3bc227f7e9de112fbf4eed11fdfa77608fefd3ba423fbe99a553fdf4cd111fefa66688ff7d333427fbe999823fdf4ccc117efa665ccff7d332645ff6956333ffd4ab111ff7a55888fff92ac227fde956113dff4aad137f7a55688ffbd2ab047fde955733fef4aa9917f7a554847fbd2a9027ff68ce223ffb467089effa33689bfed19b045ffa8cd522ffb4669917fda334c47ff519a425ff68cd211ffe445089ffea22844fff5113427bfe889a13ffe444a88ffea224c47ff51110277fe6ad873bff356c29dff9ab608effcd5b0277fe6ad723bff356b89dff9ab594effcd5ac477fe6ad613bff356a91dff9ab484effcd590477fe6ac813bff356291dff9ab144fdfcd45107f7e6a2773fdf351331ff79a8954f7fcd44aa7bfe6a2551ffd351111fff1a8844f7fcd434e5bfe6a1a62dff350d296ff9a869477fcd43465bfe6a1a21dff350c39eff9a861c77fcd43047bfe6a1813dff350bb1eff9a85d877fcd42ea7bfe6a1751dff350b99eff9a85cc77fcd42e47bfe6a1721dff350b89eff9a85c477fcd42ca7bfe6a1651dff350b10eff9a8584f7fcd42a2dbfe6a1316dff350290eff9a80c9b7fcd40643fbe69e663fef34f2a9eff9a78ccbff4d3c447ffc69e113dff34f0896ff9a7698b7fcd3b4a5bfe69da51dff34ed10eff9a7684b7fcd3b0c7bfe69d856dff34ec29eff9a760cf7fcd3b023f7e69d712dff34eb296ff9a758cf7fcd3ac27bfe69d533dff34ea89eff9a7544bff8d3aa23bfe69d313dff34e90b6ff9a7484fff4d3a425bfe69d211dff34e4196ff9a720c7ff4d34445ffc69a113dff34cd097ef9a6594bf7cd32c65fbe699612ffd34ca916ff9a6294bfbcd2caa7ffa696222dff34b0896ff9a568c77fcd2b425bfe695856dff34ab9b6ff9a55ccf7fcd2ae65bfe695731dff34ab91eff9a55c4b7fcd2aca7bfe695652dff34ab19eff9a558c77fcd2ac47bfe695622dff34ab09eff9a5584b7fcd2aa4dbfe695523fef34aa896ff9a520cb7fcd29047bfe694812dff34a1937fe9a3888b7fcd1b443bfe68da12dff346b9b6ff9a35c9b7fcd1aa6dbfe68d516ffe346a88eff9a34c9b7fcd1a62dff668d312dff34690b6ff9a3284bff4d14447ffc68a113dff345089eff9a2608f7fcd12e27bfe689623dff344b09eff9a2548f7fcd1264dbfe689316ffe343089eff9a1604f7fcd0ae27bfe62da53dff316d11eff98b684effcc5aec77fe62d756bff316ba9dff98b5cdaffcc5ae677fe62d732bff316b935ff98b5c5affcc5ae257fe62d711bff316b29dff98b58ceffcc5ac457fe62d613bff316a9b7fd98b54cfff4c5aa457fe62d522bff316a89fff18b5446ffcc5aa237fe62d326bff3169917fd98b4c4effcc5a6237fe62d216ffd3169095ff98b4846ffcc58a6d7fe else 0xc991fefa66484bf7d330a47fde955833fef4aac08ff7a554c8ffbd2aa627fde955212fef4aa109ffda336047fed19aa23ff68cd212ffb466409ffda33148ffed198427ffa889811ffd444a88ffda224c4effcd590a77fe6ac213dff350d38eff9a8694f7fcd43463bfe6a1a23dff350d09eff9a85c5b7fcd42c67bfe6a1623dff350a936ff9a8548f7fcd42a43ffc6a1511dff350291eff9a8084f7fcd3b465bfe69da31dff34ec09eff9a7604befcd3ae65bfe69d653dff34eb28eff9a7588f7fcd3aa65ffa69d522dff34ea8b6ff9a74c8ffecd3a627bfe69c813dff34cd296ff9a668cbfecd32a67bfe695a32dff34ad11eff9a5684f7fcd2b027bfe695812dff34ab8b6ff9a55c4fff4d2a425bfe694813dff34a109eff9a360db7fcd1ae2dbfe68d526ffd346a917fe9a3484b7fcd18a4dbfe689a13dff344c136ff9a2604f7fcd12e2dbfe689526dff344a8b7ff1a254477fcd110277fe62d723bff316b89dff98b588effcc5aa677fe62d526bff316a91dff98b545affcc5a6477fe62d316bff316989dff98b484effcc5a425bfe61da26fef30aa99ffe983888fff8c1c227efe609812ffe30298b7ff1814c4ffecc0a627ffc605311dff2f6d11dff97b4c8effcbda62d7fe5ed313bff2f69895ff97b204f7fcb9b44dbfe5cda23fdf2e6b1b7fd97358cffecb9a627bfe5ada13bff2d6a99dff96b54c6ffcb5aa477fe5ad313bff2d6291eff965684ff7cb2ae2dfbe595622ffb2caa99fef965549bf7cb2a62dfbe58d623fdf2c6a9b7fd96354cff7cb12c257fe56d323bff2b6989dff95b484bff4a9c447ffc54e113ffb2a6d11ff7953548ffeca9a647bfe549a13ffe2a2988dff93b484effc9d94257fe4ec852bff276411ffe932888fff8994227ff64c9312ffe262909ffd931484effc9590a57fe4ac851bff2564195ff92b20c6ffc958a65ffa46d522bff2364295ff91b20caffc8d9063ff622d313ffb10b199ffe885888fff842c227bfe215a23dff10ad09eff852684ffec15aa67bfeaeda81bff576d40dffabb69c6ffd5db4c5bfeaeda52bff576d195ffabb614effd5db0457feaed813bff576c095ffabb6046ffd5dae657feaed716bff576b89dffabb5c4affd5daca77feaed651bff576b11dffabb588affd5dac437feaed536bff576a91dffabb545affd5daa257feaed322bff576988dffabb484f7fd555107bfeaaa553dff555111effaaa844f7fd553047bfeaa9813dff554b296ffaaa584b7fd552a47bfeaa9521dff554a896ffaaa4c4b7fd5510a5bfeaa8832dff554418effaaa208f7fd550a65f7ea22773fef5112a9fbfa88954ffed444667ffaa22223f7f511111fff288844fdfd444227efea21a73f7f510d29effa88694fdfd443447efea21823f7f510c117bfa88604bdfd442e67efea21716f7f5109917bfa884c5) else (if i<12 then 0xc172e05c2416e405afc169a059d41650058ac16060578415bc0565c15720553415280540c14de052e41496c51d21452450c0140dc4fae13c944e9c1384c4d8a134044c7812fbc4b6612b744a541272c4942122e4483011e9c471e11a54460c1160c44fa111c443e810d7c42d61093441c4104ec40b2100a43fa00fc5c3e8e0f8143d7c0f3cc3c6a0ef843b580eb3c3a460e6f439340e2ac38220de9037260daa0362a0d6b0352e0d2c034320ced033360cae0323a0c6f0313e0c30030420bf102f460bb202e4a0b7302d4e0b3402c520af502b560ab602a5a0a770295e0a380286209f90276609ba0266a097b0256e093c0247208ffc238c08c6422a6088cc21c00853420da0819c1ff407e041f0e07a6c1e28076d41d420733c1c5c06fa41b7606c0c1a900687419b50653418e5061f4181505eb4174505b7416750583415a5054f414d5051b4140504e74133504b341265047f41195044b410c5041740ff503e340f2503af40e55037b40d85034740cb5031340be502df40b1502ab40a50027cc0996024e408dc021fc082201f14076801c2c06ae0194405f40165c053a013a004960111003f200e80035900c4802cb00a10023d0080401c500624014d0044400e0002bc007e00003ff4a924257fe62c326ffb306a99ffd97354cffecb1a627ff64c9313f7f510a917efa66548bfbd2aaa67fde955522ffb466a917fd9a854cffecd3aa67ff6699313ffb344989fff1815447fecb9a647ffc5c5511ffd2c49097ff152844bfbca92a25ffc545211ffe263089ffe931484b7fd5db5077feaeda83bff576d39dffabb698effd5db4a7bfeaeda23bff576d11dffabb684ffed5daa677feaed533ffd576a915ffabb548affd5daa27ff6aed313bff576989fbfa8854cff7d332627ffa889313dff350d39eff9a8698ffecd42627bfe69da63dff34ed29eff9a7688f7fcd3b427bfe699a53dff34cd11eff9a6684fff4d32425ff6695313bff316109eff985689bf7cc2acadbfe60da26fdf306b1b7fd98358cffecc1a627ffa609522ffd3049915ff97b20caffcbd9025ffa5c5212bff2d6290dff96b0c87f7cb2aa6dfbe58d622fdf2c698b7fe962548bff4ada425ff654da13ffb2a6989ffe9524c8affc9d90a77fe4ec813bff276291dff93b144effc9d8427ffa4c9212ffe262908dff92b214effc8d864dff622d533ffb056989effabb694effd5db463bfeaeda13bff576c19dffabb5cceffd5dae237feaed633bff576991dffabb4c5b7fd5534c5bfeaa9a52dff554d196ffaaa604bff5552a45bfeaa8853dff554409effaaa148f7fd550427efea21833f7f510c08ffda8854cfdfd442a23efea21323f7f510989fbfa88484bdfd440427f7e9dd833fbf4eec08fdfa7754cfefd3baa23f7e9dd323fbf4ee989fdfa77204ff7d333067fbe999533fdf4c else 0xbd421f5083d41ff507bd41df5073d41bf506bd419f5063d417f505bd415f5053d413f504bd411f5043d40ff503bd40df5033d40bf502bd409f5023d407f501bd405f5013d403f500bd401f5003d3fff4ffbd3fdf4ff3d3fbf4febd3f9f4fe3d3f7f4fdbd3f5f4fd3d3f3f4fcbd3f1f4fc3d3eff4fbbd3edf4fb3d3ebf4fabd3e9f4fa3d3e7f4f9bd3e5f4f93d3e3f4f8bd3e1f4f83d3dff4f7bd3ddf4f73d3dbf4f6bd3d9f4f63d3d7f4f5bd3d5f4f53d3d3f4f4bd3d1f4f43d3cff4f3bd3cdf4f33d3cbf4f2bd3c9f4f23d3c7f4f1bd3c5f4f13d3c3f4f0bd3c1f4f03d3bff4efbd3bdf4ef3d3bbf4eebd3b9f4ee3d3b7f4edbd3b5f4ed3d3b3f4ecbd3b2a4ec953b204ec6d3b164ec453b0c4ec1d3b024ebf53af84ebcd3aee4eba53ae44eb7d3ada4e78d38ec4e02d37354d97d35894d2cd33dd4cc1d323c4c5c530a64bf6d2f104b9152d7a4b2bd2be44ac652a4e4a60d28b849fb527224995d258c4930523f648cad226b486ad20eb480ad1f6b47aad1deb474ad1c6b46ead1aeb468ad196b462ad17eb45cad166b456ad14eb450ad136b44aad11eb444ad106b43ead0eeb438ad0d6b432ad0beb42cad0a6b426ad08eb420ad076b41aad05eb414ad046b40ead02eb408ad016b402acffeb3fcacfe6b3f6acfceb3f0acfb6b3ead8fa013e530f8973df88f72d3d9e0f5c33d438f4593ce90f2ef3c8e8f1853c340f01b3bd98eeb13b7f0ed473b248ebdd3aca0ea733a6f8e9093a150e79f39ba8e63539600e4cb39058e36138ab0e1f738508e08d37f60df23379b8ddb937410dc4f36e68dae5368c0d97b36318d81135d70d6a7357c8d53d35220d3d334c78d269346d0d0ff34128cf9533b80ce2b335d8ccc133030cb5732a88c9ed324e0c88331f38c71931990c5af31414c45b30ec4c30730974c1b330424c05f2fed4bf0b2f984bdb72f434bc632eee4bb0f2e994b9bb2e444b8672def4b7132d9a4b5bf2d454b46b2cf04b3172c9b4b1c32c464b06f2bf14af1b2b9c4adc72b474ac732af24ab1f2a9d4a9cb2a484a87729f34a723299e4a5cf294c0a49128fc8a35328ad0a215285d8a0d7280e09f9927be89e5b276f09d1d271f89bdf26d009aa126808996326310982525e1896e72592095a925428946b24f30932d24a3891ef2454090b1240488f7323b508e35236588cf7231608bb922c688a7b22770893d2227887ff21d8086c121888858321390844520e988307209a081c9204a8808b1ffb07f4d1fab87e0f1f5c07cd11f0c87b931ebd07a551e6d879171e1e077e41dd4076bc1d8a075941d400746c1cf6073441cac0721c1c62070f41c1806fcc1bce06ea41b8406d7c1b3a06c541af006b2c1aa606a041a5c068dc1a12067b419c80668c197e0656419340643c18ea0631418a0061ec1856060c4180c05f9c17c205e74177805d4)) else (if i<15 then (if i<14 then 0xa35be216f6d5bd496f375bc716f015bb996ecb5bac16e955b9e96e5f5b9116e295b8396df35b7616dbd5b6896d875b5b16d515b4d96d1b5b4016ce55b3296caf5b2516c795b1796c435b0a16c0d5afc96bd75aef16ba15ae196b6b5ad416b355ac696aff5ab916ac95aab96a935a9e16a5d5a9096a275a83169f15a75969bb5a68169855a5a9694f5a4d169195a3f968e35a32168ad5a24968775a17168415a099680b59fc167d559ee9679f59e11676959d39673359c6166fd59b8966c759ab16691599d9665b5990166255982965ef5975165b9596796583595a1654d594c96517593f164e15931964ab59241647559169643f59091640958fb963d358ee1639d58e09636758d31633158c5962fb58b8162c558aa9628f589d16259588f962235882161ed5874961b758671618158599614b584c16115583e960df5831160a958239607358161603d58089600757fb15fd157ed95f9b57e015f6557d295f2f57c515ef957b795ec357aa15e8d579c95e57578f15e21578195deb577415db5576695d7f575915d49574b95d13573e15cdd573095ca7572315c71571595c3b570815c0556fa95bcf56ed15b9956df95b6356d215b2d56c495af756b715ac156a995a8b569c15a55568e95a1f5681159e95673959b356661597d565895947564b15911563d958db5630158a556229586f56151583956079580355fa157cd55ec9579755df1576155d19572b55c4156f555b6956bf55a915689559b95653558e1561d5580955e75573155b155659557b555815545554a9550f553d154d9552f954a355221546d55149543755071540154f9953cb54ec1539554de9535f54d11532954c3952f354b6152bd54a895287549b15251548d9521b5480151e55472951af546515179545795143544a1510d543c950d7542f150a154219506b541415035540694fff53f914fc953eb94f9353de14f5d53d094f2753c314ef153b594ebb53a814e85539a94e4f538d14e19537f94de3537214dad536494d77535714d41534994d0b533c14cd5532e94c9f532114c69531394c33530614bfd52f894bc752eb14b9152dd94b5b52d014b2552c294aef52b514ab952a794a83529a14a4d528c94a17527f149e15271949ab52641497552569493f524914909523b948d3522e1489d5220948675213148315205947fb51f8147c551ea9478f51dd1475951cf9472351c2146ed51b4946b751a71468151999464b518c14615517e945df5173d45bf516bd459f5163d457f515bd455f5153d453f514bd451f5143d44ff513bd44df5133d44bf512bd449f5123d447f511bd445f5113d443f510bd441f5103d43ff50fbd43df50f3d43bf50ebd439f50e3d437f50dbd435f50d3d433f50cbd431f50c3d42ff50bbd42df50b3d42bf50abd429f50a3d427f509bd425f5093d423f508 else 0xc8daefd6bb5daeb16ba2dae656b8fdae196b7cdadcd6b69dad816b56dad356b43dace96b30dac9d6b1ddac516b0adac056af7dabb96ae4dab6d6ad1dab216abedaad56aabdaa896a98daa3d6a85da9f16a72da9a56a5fda9596a4cda90d6a39da8c16a26da8756a13da8296a00da7dd69edda79169dada74569c7da6f969b4da6ad69a1da661698eda615697bda5c96968da57d6955da5316942da4e5692fda499691cda44d6909da40168f6da3b568e3da36968d0da31d68bdda2d168aada2856897da2396884da1ed6871da1a1685eda155684bda1096838da0bd6825da0716812da02567ffd9fd967ecd9f8d67d9d9f4167c6d9ef567b3d9ea967a0d9e5d678dd9e11677ad9dc56767d9d796754d9d2d6741d9ce1672ed9c95671bd9c496708d9bfd66f5d9bb166e2d9b6566cfd9b1966bcd9acd66a9d9a816696d9a356683d99e96670d999d665dd9951664ad99056637d98b96624d986d6611d982165fed97d565ebd978965d8d973d65c5d96f165b2d96a5659fd9659658cd960d6579d95c16566d95756553d95296540d94dd652dd9491651ad94456507d93f964f4d93ad64e1d936164ced931564bbd92c964a8d927d6495d92316482d91e5646fd9199645cd914d6449d91016436d90b56423d90696410d901d63fdd8fd163ead8f8563d7d8f3963c4d8eed63b1d8ea1639ed8e55638bd8e096378d8dbd6365d8d716352d8d25633fd8cd9632cd8c8d6319d8c416306d8bf562f3d8ba962e0d8b5d62cdd8b1162bad8ac562a7d8a796294d8a2d6281d89e1626ed8995625bd89496248d88fd6235d88b16222d8865620fd881961fcd87cd61e9d878161d6d873561c3d86e961b0d869d619dd8651618ad86056177d85b96164d856d6151d8521613ed84d5612bd84896118d843d6105d83f160f2d83a560dfd835960ccd830d60b9d82c160a6d82756093d82296080d81dd606dd8191605ad81456047d80f96034d80ad6021d8061600ed80155ffbd7fc95fe8d7f7d5fd5d7f315fc2d7ee55fafd7e995f9cd7e4d5f89d7e015f76d7db55f63d7d695f50d7d1d5f3dd7cd15f2ad7c855f17d7c395f04d7bed5ef1d7ba15eded7b555ecbd7b095eb8d7abd5ea5d7a715e92d7a255e7fd79d95e6cd798d5e5c979575e4f179215e41978eb5e34178b55e269787f5e19178495e0b978135dfe177dd5df0977a75de3177715dd59773b5dc8177055dba976cf5dad176995d9f976635d921762d5d84975f75d77175c15d699758b5d5c175555d4e9751f5d41174e95d33974b35d261747d5d18974475d0b174115cfd973db5cf0173a55ce29736f5cd5173395cc7973035cba172cd5cac972975c9f172615c919722b5c84171f55c76971bf5c69171895c5b971535c4e1711d5c40970e75c33170b15c259707b5c18170455c0a9700f5bfd16fd95bef96f) else (if i<16 then 0xae27eac5fa807e93dfa1e7e7b5f9bc7e62df95a7e4a5f8f87e31df8967e195f8347e00df7d27de85f7707dcfdf70e7db75f6ac7d9edf64a7d865f5e87d6ddf5867d555f5247d3cdf4c27d245f4607d0bdf3fe7cf35f39c7cdadf33a7cc25f2d87ca9df2767c915f2147c78df1b27c605f1507c47df0ee7c2f5f08c7c16df02a7bfe5efc87be5def667bcd5ef047bb4deea27b9c5ee407b83dedde7b6b5ed7c7b52ded1a7b3a5ecb87b21dec567b095ebf47af0deb927ad85eb307abfdeace7aa75ea6c7a8edea0a7a765e9a87a5dde9467a455e8e47a2cde8827a145e82079fbde7be79e35e75c79cade6fa79b25e6987999de63679815e5d47968de57279505e5107937de4ae791f5e44c7906de3ea78ee5e38878d5de32678bd5e2c478a4de262788c5e2007873de19e785b5e13c7842de0da782a5e0787811de01677f95dfb477e0ddf5277c85def077afdde8e77975de2c777edddca77665dd68774dddd0677355dca4771cddc4277045dbe076ebddb7e76d35db1c76baddaba76a25da587689dd9f676715d9947658dd93276405d8d07627dd86e760f5d80c75f6dd7aa75de5d74875c5dd6e675ad5d6847594dd62d7581dd5e1756edd595755bdd5497548dd4fd7535dd4b17522dd465750fdd41974fcdd3cd74e9dd38174d6dd33574c3dd2e974b0dd29d749ddd251748add2057477dd1b97464dd16d7451dd121743edd0d5742bdd0897418dd03d7405dcff173f2dcfa573dfdcf5973ccdcf0d73b9dcec173a6dce757393dce297380dcddd736ddcd91735adcd457347dccf97334dccad7321dcc61730edcc1572fbdcbc972e8dcb7d72d5dcb3172c2dcae572afdca99729cdca4d7289dca017276dc9b57263dc9697250dc91d723ddc8d1722adc8857217dc8397204dc7ed71f1dc7a171dedc75571cbdc70971b8dc6bd71a5dc6717192dc625717fdc5d9716cdc58d7159dc5417146dc4f57133dc4a97120dc45d710ddc41170fadc3c570e7dc37970d4dc32d70c1dc2e170aedc295709bdc2497088dc1fd7075dc1b17062dc165704fdc119703cdc0cd7029dc0817016dc0357003dbfe96ff0dbf9d6fdddbf516fcadbf056fb7dbeb96fa4dbe6d6f91dbe216f7edbdd56f6bdbd896f58dbd3d6f45dbcf16f32dbca56f1fdbc596f0cdbc0d6ef9dbbc16ee6dbb756ed3dbb296ec0dbadd6eaddba916e9adba456e87db9f96e74db9ad6e61db9616e4edb9156e3bdb8c96e28db87d6e15db8316e02db7e56defdb7996ddcdb74d6dc9db7016db6db6b56da3db6696d90db61d6d7ddb5d16d6adb5856d57db5396d44db4ed6d31db4a16d1edb4556d0bdb4096cf8db3bd6ce5db3716cd2db3256cbfdb2d96cacdb28d6c99db2416c86db1f56c73db1a96c60db15d6c4ddb1116c3adb0c56c27db0796c14db02d6c01dafe16beedaf956bdbdaf496b else (if i<17 then 0x6ba65aa29696e5a14967365986964fe58f8962f2588096112580895f32579095d52571895b7256a0959925628957b255b0955d25538953f254c09521254489503253d094e52535894c7252e094a925268948b251f0946d25178944f2510094312508894132501093f524f9893d724f2093b924ea8939b24e30937d24db8935f24d40934124cc8932324c50930524bd892e724b6092c924ae892ab24a70928d249f8926f2498092512490892332489092152481891f7247a091d92472891bb246b0919d24638917f245c09161245489143244d09125244589107243e090e92436890cb242f090ad24278908f242009071241889053241109035240989017240208ff923fa88fdb23f308fbd23eb88f9f23e408f8123dc88f6323d508f4523cd88f2723c608f0923be88eeb23b708ecd23af88eaf23a808e9123a088e73239908e55239188e37238a08e19238288dfb237b08ddd237388dbf236c08da1236488d83235d08d65235588d47234e08d29234688d0b233f08ced233788ccf233008cb1232888c93232108c75231988c57231208c39230a88c1b230308bfd22fb88bdf22f408bc122ec88ba322e508b8522dd88b6722d608b4922ce88b2b22c708b0d22bf88aef22b808ad3e2b1e8abb62abc8aa2e2a5a8a8a629f88a71e29968a59629348a40e28d28a28628708a0fe280e89f7627ac89dee274a89c6626e889ade2686899562624897ce25c2896462560894be24fe89336249c891ae243a8902623d888e9e237688d16231488b8e22b288a0622508887e21ee886f6218c8856e212a883e620c88825e2066880d6200487f4e1fa287dc61f4087c3e1ede87ab61e7c8792e1e1a877a61db88761e1d56874961cf48730e1c92871861c3086ffe1bce86e761b6c86cee1b0a86b661aa8869de1a468685619e4866ce1982865461920863be18be86236185c860ae17fa85f26179885d9e173685c1616d485a8e16728590616108577e15ae855f6154c8546e14ea852e614888515e142684fd613c484e4e136284cc6130084b3e129e849b6123c8482e11da846a611788451e11168439610b48420e1052840860ff083efe0f8e83d760f2c83bee0eca83a660e68838de0e06837560da4835ce0d42834460ce0832be0c7e831360c1c82fae0bba82e260b5882c9e0af682b160a948298e0a328280609d08267e096e824f6090c8236e08aa821e608488205e07e681ed6078481d4e072281bc606c081a3e065e818b605fc8172e059a815a605388141e04d68129604748110e041280f8603b080dfe034e80c7602ec80aee028a809660228807de01c6806560164804ce01028034600a0801be003e80035ffdc7feadff7a7fd25ff187fb9dfeb67fa15fe547f88dfdf27f705fd907f57dfd2e7f3f5fccc7f26dfc6a7f0e5fc087ef5dfba67edd5fb447ec4df else 0x22142a05c08813c070050b204623b05088c0901380380484502a23305088c0901380380482804a26705085c0901380380485385182a44407c090138038048b885182a03c85c090138038048b882d82a03485c09013803804990c1522203e04808e0f803804990c1522202e04808e0f8038048b382b82a44405c0901380380483f85182a03c85c0901380380484a0780d411992c146270270048b303864305088c08e0fc070048b306064305088c08e0fc070048b813323305085c09a0bc070048b813323305085c09a0bc0700489f1292330558910b813c070048b813323305085c09a0bc0700485304a27b0540710f813c070048b816e0970540710f813c0700489a02a23305405c08e0bc070048b345182944207c088138058048b31640970520710f813c0700483c46582944206c0881380580484506408f0520610d813c0700483f04a25b0520710f813c0700483c04605b0540610d813c0700483c05608cc860a31101b0270048504506490518911281d027804850324828c488900e81002780482804a86d0518710e819027804a280466390520730c21902780482331c8280398610c81002780483c02a6310520630a2150278048530580941020a90e81002780483f04c0800ac8c415215020044990c1422143a07c08813c0700498cc14a1d03885c08813c07004a8ec1422143206c08813c0700482804b82844604809c01c0221960a91101b02404e00e0110570548880b81202700700885182a03c85c09013803804428c1522203e04809c01c0221960a91101b02404e00e0110a30540790b81202700700882d82a03485c09013803804432c1522203604809c01c0220ae0a91101702404e00e01105b0540690b8120270070080780ac11990c1462302700404a07808c0be0a30f81380211460a51081f02204e0160100c811e0a80c21b02780e00816607705088c09e03801c1b8b3c1422302780e00706426705085c09e03801c4c817c1421702780e00708e27c4c89402882b411c4ce0a10b813c070030b3c1422302780e006c1501f02004f01c00d82a03604009e0380182284303205505204305409e0d41020a284707e0981020a284704082a43d8228530580a105204284707e099052042853058081051022820415e04808105007d02404a24d05487c09e0fc1381303e03802e72069c6a6714c9c3be70929c0d66fe39be466f3f9bbb66e9b9b9266df79b6966d539b4066caf9b1766c0b9aee66b679ac566ac39a9c66a2a9a78e699c9a556690e9a31e68809a0e667f299eae676499c7666d699a3e66489980665ba995ce652c99396649e9915e641098f26638298cee62f498ab662669887e61d898646614a9840e60bc981d6602e97f9e5fa097d665f1297b2e5e84978f65df6976be5d68974865cda9724e5c4c970165bbe96dde5b309))))) else (if i<27 then (if i<22 then (if i<20 then (if i<19 then 0x940f80e00c0940f01181631982a03185c09e0fc07006032160270c828ec15811c1f82f03e0380301b8af1346494660ac09e0dc1781f01c0181144f894d24a3305604f07a0bc0f80e00c08b0570548890b01442e04009c01c02c1e0231322584760a10b81202700700b13f82844c8790d81241c82903c01c02c4fe0a1132224360490720a40f00700bc1522644486c08e0c41c82903c01c02e1760ab1321f42e0480920a01700700b9190330558990b81202482805c01c02c1919011d82a44406c09011c1f00700b0950584760a80d21702404707c01c02f0548990d2170248370420a40f00700b16782a4488890d81241c82903c01c02e1760ab1321f42e0480920a01700700b9190330558990b81202482805c01c02e0b60a91322043e0490720a40f00700b9190330558990b81202482805c01c02c4d894c1421c42e0410620840f80e00b1362530508710d81041882103e03802c4d894c142204360410620840f80e00b1362530508810f81041882103e03802c4d894c1422442e0410620840f80e00b1362530508910d81041882103e03802c4d894c1422443e0410620840f80e00b1678284428750b81141a82503c02c02c27e0a51021d42e04506a0940f00b00b46f8294408750d81141a82503c02c02c4ce0a510a1c42e04506a0940f00b00b1702644901291982842e04d05e03802c4c89412404b05189110a1702780e00b13225049012c1462443a85c09e03802c5989b11c03b0528810f21b02780e00b4658294488750b81141a82503c02c02c4de0a51221942e04506a0940f00b00b13782944a8710d81141a82503c02c02c4ce0a512a1842e04506a0940f00b00b0940f011816319828c2e04705e03802d1760a712a1f42e04408a0901700b00b07808d0ca1531c828c308640a813c02c1e0232286390518610c01502004f00b51c6330528640c61442e04409e03802c1e592c15818c2e04f0760bc0f80e00b85182a4448780e21f02004e00e0142cf0548890d01843604009c01c02a1460a90f01c43c85c0801380380503cc1521a0308690b81002700700a82a2330548880b81202382e00e01411cc660a80f21702404705c01c02a0b18cc1501a42e04808e0b8038050b33202380760a111811c1f80e00ac14a2443a86c08a0d41281e0160140c8c809011d82a03604707e0380285802302c23b05406c08e0fc0700509f1322530538911121702780e00a13e2644a60a71221e42e04f01c014114598b202b82a02885c09e03802814025036828c388700c81002780503c02a6310500630a21502004f00a08e27c4c89402882902682005e014150278350460824720a90c81002282389f1322500a4924148124100250450400564620a90a81002681f00a08e0fc1302504082a43a04009e0140acc808ec1522203604707e038028c828cc14 else 0x344da1ac14a254388650b81141e82503c02c0345c09f13a24b05189d0b81241402105e0380342502313e6304660ac0c61702783f03e03803459a2e435829c4a88d0b81102282405c02c0345c099119829c4a8890b81102282405c02c0345c099119829c4a8790b81102282405c02c0340b98ec146204420710e61843604009e0380341e016319828c488940c61442e04009e0380340b990c146204418710e81843604009e0380341e016319828c388740c61442e04009e0380341e02302c6330520610c61442e04409c02c034c960a312a2143a85c0881141a82503e038034c860a51262143a85c0881141a82503e0380342989fc1422643485c0920e41481e00e0190c84fe0a11321e42e0490720a40f00700c13f05f050899112170248390520780380609f82d82844c8890f81241c82903c01c030c860a91321a42e0470620e41481e00e0186430548990f21b0238310720a40f00700cc152264448690b811c1883d05207803806432c1522643c85c0920dc1082903c01c0314660a91321e43604906e0841481e00e01905f054899112170248370420a40f00700c16782a4488890d21702483d052078038060b382f82a4488890b81241c82903c01c03059c16c1522444487c0920e41481e00e0190bf0548991021e42e04907a0a40f00700c07e26f0548991021b0248390520780380642e9190330558990b81202482805c01c0302989b12982843085c0820c41081f01c01813c4d894c1422042e0410620840f80e00c07e26c4a60a11222302083104207c0700621dc14a2143285c0960c41a82503c02c0324760a510a1d42e04b0620d41281e0160188df0528850ea1b02583106a0940f00b00c1668770508850ca1702283504a078058062371678284428750d81141a82503c02c0310e89bc14a2043285c08a0d41281e0160188dc4de0a510a1c43604506a0940f00b00c43a2670528850c21702283504a07805806230c14a254408750d811c1a82503c02c0305989b1322380760a51121842e04f01c01886b0528910ea1942e04507a0940f00b00c4642670528950e21702283504a0780580609bc14a254408650b81141e82503c02c0304ca17c14a2544085c08a0d41281e0160181281198cc15818c2e04f07e0bc0f80e00c09408c4d98cc15818c2e04f05e07c0700609f13225305189d0b81002282405e0380304f894119828c4c85c0801141202f01c01827c4a08cc1462642e04008a0901780e00c45c86b05389511a170220450480b8058060b805c2644660a90b81141202105e0380305c02e13223305485c08a0901082f01c0181281198cc15818c2e04f07e0bc0f80e00c09408cc660ac0c61702783f05e07c0700601d319828c488940e61442e04009e038030130253198290388730a21702204e01601982944a8830ea1702204506a0) else (if i<21 then 0xc0700722e42b82944a8830ea1b02204506a0940f80e00e45063b0528951061942e04408a0d41281f01c01c8a0c660a512a2143185c0881141a82503e03803b0528991181f43685c09a0f41681e01601c03705289911a1f03685c09a0f41681e01601c03705289911a1f43605c09a0f41681e01601c03705289d1121f03685c09a0f41681e01601c03705289d1121f43605c09a0f41681e01601c03705289d1181e43685c09a0f41681e01601c03705289d11a1e43605c09a0f41681e01601c0344fc1cc142264448690b812c1c82903c01c0361809fc142264448790d812c1c82903c01c0345c09f125828c4c87d0b81202482805c01c0344f8929190330518990b81202482805c01c0360b98ec1522644485c08e0c41c82903c01c0360b28ec1522644487c08e0c41c82903c01c0360d190c1562644685c09011c1c82805c01c0342398cc1522644486c0920dc1082903c01c0360b18cc1522644487c0920dc1082903c01c0370568951121f03685c09a0f41681e01601c0370568951121f43605c09a0f41681e01601c0370568951181f43485c09a0f41681e01601c03705689511a1f03485c09a0f41681e01601c03459c2fc152244448790b81241e82903c01c03416025321828c408890f01c43e04809c01c03415823321828c408890d01843604809c01c03422815321828c408890b01442e04809c01c03705689d10a1e43605c09a0f41681e01601c03705689d10a1f03485c09a0f41681e01601c03411817c152264428790b81241c82903c01c03413015c152264428790d81241c82903c01c03705689d1181d43485c09a0f41681e01601c0345989b1298284408610b812c1882103e0380345989b1298284408710d812c1882103e0380344c8949258284388610b81041e82103e0380344c8949258284408610b81041e82103e0380344c8949258284408710b81041e82103e0380344a4929198284408710d81041e82103e0380344d8943218284488610b812c1882103e0380344d8943218284488710d812c1882103e0380345989b1298284488810d812c1882103e0380344f8991298284488610b81041e82103e0380344f8991298284488710b81041e82103e0380344f8949198284488710d81041e82103e0380344f8991298284488810b81041e82103e0380344f8949198284488810d81041e82103e0380344f8949198284488810f81041e82103e0380350e992c14a2143285c08a0ec1082503c02c0342a192c14a2143a85c08a0ec1082503c02c03549212c14a2043a8650b81141e82503c02c0342801dc14a2243a8650b81141a82503c02c0350e60a512a2143285c08e0ec1082503c02c0354720ec14a254408750b811c1a82503c02c0350e099c14a254428610b811c1a82503c02c0341682cc14a2643a8650b81141a82503c02c0 else 0x6d0b81341b82505a0780580700ec15a2544487d0da1702683d0580b40f00b00e01c2cf0568951181e43685c09a0f41681e01601c03859e0ad12a2343c86c0b81341e82d03c02c0380760ad13a2143c86d0b81341e82c05a0780580700e85d2320660a91322043c86c0920f41481e00e01c2cc4d89491d8284408710b812c1882103e0380384d89432123b0508910e21702583104207c070070b3136250c760a11222042e04b0620840f80e00e16626c4a48ec1422444087c0960c41081f01c01c0940e992c146254428650b81141a82503c02c0381a823325828c4a8850ea1702283504a0780580703402a64b05189510a1d43604506a0940f00b00e52484b0528850ea1942e04b0620f41281e01601c0dcc948cc14a2143a86c08a0ec1082503c02c03859a924258284428750ca1702283d04a0780580709b52484b0528850e21942e04507a0940f00b00e0a00d64760a510a1e43285c08a0d41281e01601c1401a48cc14a2143a8690b81141a82503c02c0394720ec14a254428750b811c1d82104a0780580723091982944a8850ea1b02383b0420940f00b00e166870c860a51222143285c08e0d41281e01601c2cd18190c14a244428750d811c1a82503c02c03948a11c14a254408750ca1702383d04a0780580704a03982944a8890ea1942e04706a0940f00b00e16626cc760a512a2043285c08e0d41281e01601c2cc4d98ec14a254428710d811c1a82503c02c0384ca8e41d82944a8850e21702383504a078058070b816626c4c8910232330528810b81341780e00e16627c4c894122044c860a110a1702383f01c01c0b012990c14a24c428650b81141a82503c02c038158233218294498850ea1702283504a0780580704502a64305289310a1d43604506a0940f00b00e05a0ae4760a512a1e43285c08a0d41281e01601c2e04cc8cc14a2543a8610b81141e82503c02c0382282d91982944a8750d21702283504a0780580704705d82944a8830ea1942e04507a0940f00b00e1702664660a512a2143085c08a0f41281e01601c0940b98ec14a254418650b81141a82503c02c0385c09991982944a8850e21702283d04a0780580702604a63305289510a18c2e04506a0940f00b00e17027c4f01a125828c4e85c0920a01082f01c01c1281e02313a2704de0a30f81b02782f03e0380382503c0462744c894c1461f03604f07e07c0700704705d829c498710fa170220450480841700b00e0780a41189e13064105188c0d813c1f82f01c01c12814827046260c620ac0c61702783f05e0380381e01631d828c408830c21902885c08013c07007228325828c4a8850ca1702204506a0940f80e00e42a64b05189510a1d43604408a0d41281f01c01c8a0c860a51262143285c0881141a82503e0380391760a512a2143285c0881141e82504a07)) else (if i<24 then (if i<23 then 0x798cc15a2744607d0d21702683704a0b40f00b00e01e63305689d11a1f03485c09a0dc1282d03c02c038078b3c15a254468790da1702683d0580b40f00b00e01e2ce1748c81982a4488890f21b02483d05207803807c2e1372320660a91322243886c0920f41481e00e01e0f00b01551d82a44c8890ea1b0248390520780380789952484a4660a510a1d43085c08a0f41281e01601e2ccc828e41d8294488850ea1702383504a0780580784a06123305289510a1d43485c08e0d41281e01601e0b80d190c14a24c428750ca1702283d04a0780580782f05c63b05289510a1cc3285c08a0f41281e01601e0f01181631982944a8850e61702283504a078058078b805c27e4a09211803305189c0920a01082f01c01e0f01189e1342644a190c1462303604f07e07c07007992125828c4889d1061c43e06d0b81341e81f01c01e6484960a3122274418710fa1b02e04d07a07c0700782e0346430538931022342e04408a0901082e01601e278c960a312224c3887c0da1702683d05a07c0700789e325828c488930e21f43605c09a0f41681f01c01e648c588b3122274418710f81b42e04d07a0bc0700799231622cc4889d1061c43e86c0b81341e82f01c01e098c818cc146204420710e61442e04009a07c07007897325828c4889d1061c43e05c09a0f41681f01c01e0f00b190319828c408840c218c2885c08013c070078b7325828c4889d1061c43e06c09a0f41681f01c01e11413190c146204418710e81442e04009a0bc07007a2e32182944a8750ca1702204507a0941281f01c01e8b90a990c14a24c428750d81102283504a07c07007a2e31d82944a8850ea1702204507a0941281f01c01e8b90a98ec14a254428730d81102283504a07c0700783c31982944a8850e61702204507e0941281f01c01e27c4c894c1462644685c0801241402105c01c0384f899129828c4c87d0b8100248280420b80380760a513a2303e86d0b812c1c83d05a0780580700ec14a2744687d0d81702583907a0b40f00b00e01c2e305289d1181f43485c09a0f41681e01601c0385c60a513a2343e0690b81341e82d03c02c0380709f91d03b0508991121e42e04b0720a40f00700e17027d4960a11322243485c0920f41481e00e01c2e04fc1a125828c4c88d0b81202482805c01c03b05689d1121f43605c08e0d41e82d03c02c0380760ad13a2303e8690b811c1a83d05a0780580700e8346430548990f21a42e0470620f41481e00e01c0c8c828ec1522643c85c08e0c41c82903c01c03a1798ec152264448790b811c1883d0520780380748c81982a44c8890f21b02383107a0a40f00700ec15a2644607d0da1702683704a0b40f00b00e01d82b44c88d0f81b42e04d06e0941681e01601c03b05689d1121f03685c09a0dc1282d03c02c0380760ad13a2303c8 else 0xf41602d03e0380401e09d31d82b4418710e61843605c09a0f41681f01c0202dcc718cc15a230398610c61442e04d07a0b40f80e0103246404860a312224c4088c0fa1b42e04d05a07c070081923202430518911262044687c0da1702682d03e0380404e09b325828c4889d1061c43e06d0b81341681f01c0202704d992c1462444e8830e21f43605c09a0b40f80e01016026cc660a31222744607d0c61442e04d05a07c0700818e11d82b44e8830e21cc3086d0b81341602d03e0380401e18e11d82b44e8830e21cc3086c0b81341681f01c0206384718cc15a274460730c218c2885c09a0b40f80e010324248c860a312224c4088c0fa1b42e04d07a07c070081921246430518911262044687c0da1702683d03e0380404d09431d82b4498811181cc3086d0b81341e81f01c020638c608cc15a274460730c218c2885c09a0f40f80e01016463b0568930e21cc3086d0b81341e82c05a07c0700803c16463b0568930e21cc3086c0b81341e82d03e0380405918e31982b44e0730c218c2885c09a0f41681f01c0200a44999232062444988111a1f03685c09a0f41780e01005224cc76893102234398610da1702683d0580bc0700803c05224cc76893102234398610d81702683d05e038040c718b117a274418710e61843685c09a0f41602f01c0200f0c718b117a274418710e61843605c09a0f41780e01013a648c860a312224c4088c0da1702683d05a07c070080b23246430518911262044607d0b81341e82d03e0380405b992321828c488931022303e86c09a0f41681f01c0202dcc9190c1462444988111a1f03604d07a0b40f80e01012c63b05689d1061c4398610d81341e82c05a07c0700803c046250c860a11262043885c0801041882103e0380401e02312923b0508810e21702004b0620c41081f01c0201401189b1298284408710b81041882103e03803807a8ec14a244428750ca1702204506a0940f00b00e01ea3b0528951021d43285c0881141a82503c02c03807c8ec14a2744687c0da1702583907a0b40f00b00e01e64b05289d1181f43685c09a0ec1482d03c02c03807992c14a2744687c0da1702683b0520b40f00b00e01e2e04fc1a52582844c8790d21702483d052078038078b813ea4b0538911322243c85c0920f41481e00e01e27d4948c81982844c8890f21b02483d05207803807e0ad13a2303e86d0b811c1a83b0520b40f00b00e01e6430568991181f43685c08e0d41e82d03c02c03807990c15a2644687d0d81702383507a0b40f00b00e01f82b44e8890fa1b42e04706a0f41602d03c02c03807a8ec15a2744487c0da1702383507a0b40f00b00e01e63b05689d1181e43685c08e0d41e82d03c02c0380798ec15a274468790d81702383507a0b40f00b00e01ea3b05689d11a1f03485c08e0d41e82d03c02c038) else (if i<25 then 0x408710d81041882103e0380380842d05a08c4d894c1422443885c0820c41081f01c01c04014c2804a08c4d894c142244408510620840f80e00e0200f01189b82a0544a60a11222043883104207c0700701013ea3b05089510a1d43285c0881141a82503c02c0380821551982844a8850ea1942e04408a0d41281e01601c0414760a512a2143a8650b81102283b0420940f00b00e0208a112e0a51222143a8650b81102283504a0780580701042aa330528951021d43285c0881141a82503c02c0380819291982944e88d0fa1b02e04d0760a41681e01601c0414960a712a2644687d0da1702683d0580b40f00b00e020a4b05389513a2243e86d0b81341e82c05a0780580701085182944e8890f01f43685c0901341e82d03c02c03808292c14e2544e88d0f21b42e04d07a0b01681e01601c0424760a513a2343c8680da1702404d07a0b40f00b00e020a3b05689d11a1f03685c08e0d41d82905a0780580701091982b44e88d0fa1b02e04706a0ec1482d03c02c03808190c15a2644687d0da1702383507a0b01681e01601c040c828ec15a2644687c0da1702383507a0b40f00b00e02182b44e8890f01f43685c09011c1a83d05a0780580701031d82b44e88d0f21b42e04706a0f41602d03c02c0380848cc15a2744687d0d21702383507a0b01681e01601c0411728cc15a2644687d0d81702683704a0b40f00b00e02182b44e8890f01f43685c0901341b82505a0780580701045ca3305689d1121f43605c09a0dc1282d03c02c0380822e51982b44e88d0f21b02e04d06e0941681e01601c0421460ad12a2243c07d0da1702404d07a0b40f00b00e02123b05689511a1e43406d0b81202683d05a0780580701085d23305689511a1f43485c09a0f41602d03c02c03808228c15a274428740f21b42e04409a0f41681e01601c0424760ad13a2143c8680da1702404d07a0b40f00b00e0210ba4660ad13a2143e8690b81341e82c05a0780580701045182b44e8850e81f43485c0881341e82d03c02c0380842e91982b44e88d0ea1a42e04d07a0b01681e01601c0405989b1322524960a11021c43085c0960f41081f01c02027c4d8991286430508910e21842e04b07a0840f80e01016627c4d8991298284488810c21702583d04207c070080b313e2644a18ec142244408710b812c1e82103e0380405989f1362524660a11222043886c0960f41081f01c02005cc918ec146244488830c21842e0410620840f80e01003a26cc660a3122244408630a21702083104207c0700801712864305089310220c388710b81041882103e0380400b89431d8284498811061843085c0820c41081f01c020098c818cc14224c408810c61442e0410620840f80e010166a4508990c14a244428750ca1702383d04a0780580809d31d82b4418710e61843685c09a0 else (if i<26 then 0x6a0940f00b00e0228a112899c14a254428750c21702204506a0940f00b00e0220f04ca8ec14a254428750c21702204506a0940f00b00e022a4b05389513a2343e86d0b812c1c83d0580b40f00b00e0230564660a513a2343e8690b01702404d07a0b40f00b00e0222e04fa929230470508991121e43485c0960f41481e00e02323305689d11a1f4348580b81202383507a0b40f00b00e02323b05689d11a1e43406d0b81202683704a0b40f00b00e0230564660ad13a2143e8690b01702404d07a0b40f00b00e0220f14760ad13a2343a8640d21702204d07a0b40f00b00e022074c9190c146244498811181c43085c0820c41081f01c0220acc9190c146244498811021f03085c0820c41081f01c02226c0b992c146244488830e21f03085c0820c41081f01c0220984d992c146244488830e21c43605c0820c41081f01c0220f00b19231d828c488911021cc3086c0820c41081f01c0220f04d816319828c488911021cc2885c0820c41081f01c022114130943218284498811061c43886c0820c41081f01c0220f00b09431d8284498811021cc3086c0820c41081f01c0220f00b1903198284498811021cc2885c0820c41081f01c0220f04d8163198284488830e21cc2885c0820c41081f01c02205cc718cc142244460730c218c2885c0820c41081f01c0222cc4da9142263b05289510a1c43285c08e0f41281e0160222e04ca9142323305289510a1d43085c08e0f41281e016022114c9190121828c488931022343e86c0b81341681f01c0220f05809b319828c4889d11a1f0318510b81341681f01c022114c9092321828c488931022343e86c0b81341e81f01c0220f04d09431d82b44988111a1cc3086c0b81341e81f01c0220f05789431d82b44e8830e21cc3086c0b81341e81f01c02211414893324640c488931022343e86c0b81341e82f01c0220f014827126630c4889d11a1f0318510b81341e82f01c0221144e992321828c488931022343605c09a0f41681f01c02211459192321828c488931022343e05c09a0f41681f01c02205cc960a3122274418710e81b42e04009a0f41681f01c022098c960a3122274418710fa1902e04009a0f41681f01c0221281e02313664b0518911021c42e0400820c41081f01c0221281e0231362530508911061c42e0400820c41081f01c0221281189b3198284488810e61702004107e0841081f01c0221285b8231362530508911021c42e0400820c41081f01c0220f04e09491d8284488810e21702004b0620c41081f01c0221281e0231378284488810e2170200410760841081f01c0221281e0231362530508911021c42e0400820c41081f01c0221281e0231362530508911021c42e0400820c41081f01c02214014c2804a26c4a60a11021842883104207c070070100a026e0a8151298284 else 0xcc3086d0b8100268350480841681f01c02c27c4c89431d82b44989d1061c4398610da1702004d06a0901082d03e038058228343246430518911262044687d0c81442e04009a0f41681f01c02827c4c89431d8284488830e21cc308610b81041e82c04207c0700989f1322524760a11222043c8610b8100208370460841081f01c026074c9190c146244498811081c43e86d0b81002683d05a07c0700982b324643051891126204468740c21b42e04009a0f41681f01c0260f01189491d8284488810f218c2885c0801041f82104207c0700984a08a0f0148231362530508911021c42e0400820c41081f01c0270b4168298500944d894c1422443085c0820c41081f01c01c0481702913e26c4c894c142244408610b81041e82103e038038090298500944dc1502a2530508911021b02083104207c07007012170a4a4660a712a2744687d0d21702683d0580b40f00b00e0241160ac8cc15a2544687d0d21602e04809a0f41681e01601c0481e41591982b44e88d0ea1a42c05c0901341e82d03c02c03809045068648c860a312224c408810e21b02e0410620840f80e01213e2644a190c14224c408830e21c43085c0820f41081f01c02427c4c89431d8284498811021cc308610b81041e82103e0380481e01612863b0508911061c4398610d81702083104207c0700903c0462524760a31222043c8610c2170200410620840f80e01213e2644a190c14624c408830e21f42e04008a0901082f01c0240f01189491d8284498810f21843085c0801041882103e0380481e02312923b0508911061e4308610b81002083104207c0700901731c63305689d1081cc308630a21702004d07a0b40f80e012078058c760ad13a20c388730c21902e04009a0f41681f01c0241281e02313c26c4a60a11222043885c0801041882103e0380482503c0462744d894c142244408710b81002083104207c070090cc16008c4a48ec142244408710b8100258310620840f80e0120940f01189b1358284488810e2170200410760841081f01c024128598291362530508911021842e04b0620840f80e00e0221285989b82a2530508911021c43604b0620840f80e00e0220b84f89b1322530508910e21842e04107a0840f80e00e0221161682d1370540a894c142244388610620840f80e00e0220b84f89b1322530508911021c42e04107a0840f80e00e0228a11289fc142254428750ca1702204506a0940f00b00e0228a112e0a512a2143a8650b81102583106a0940f00b00e0228554660a512a2143a8650b81102583106a0940f00b00e0228a112e0a512a2143a8650b81102283b0420940f00b00e0221150aa8cc14a244428750ca1702204506a0940f00b00e0228a11289bc14a254428710ca1702204506a0940f00b00e0220f10aa8cc14a254428710ca17022045)))) else (if i<32 then (if i<29 then (if i<28 then 0x4f7001187e00230fc005013800a02700109d504245ca0842778008c37001186e002311c004623800a027001404e002809c0048b9410a40f001089e002305c0046238008c47001404e00230fc00461f80085bb821188e00230fc004e0f8009c1f0010b35222166a444a4740884da9110995222307c005013800a027001404e002809c005013800948681109b5202136a4042654809486811404e002809c00460f8008c1f001404e002809c0048b84d884da15102e132230dc00461b800a027001183e002307c0050138008c1f001183e002132a384a3b408a027001183e002307c005013800a027001228d0221608104e0b800902700109ad02242aa084813800812e8112155042451a04485541081e0991204e002409c00501380090aa82121550420782644813800a027001404e002451a0448550209c1f001382e002047c00405780084f7001023e00205c264481380081e7001204e002409c0048138009027001186e002809c00461b8009027001404e00245ce0c4855c1880ab831204e002451a04405780080af00102e132210fc005013800a02700103c4082705c00405780084b6811382e002707c0046230208c3a061083e002c09c00421f8009027001583e002b03c005013800814a041582e00206a0804117408811f00109be002c15c00582b800855f0010abe002047c004a23408814a8810295102052a204a234089446811094e002c15c00426b800b05700160ae002c09c00581380084ca871287408210fc004265430811f001287408250e8104a1d020943a041094e002409c00425380084df001094e002139c004253800b027001286408250c8104a1902084a700160ae00215fc004253800b057001285d02250a8104a17408942a041285d022c15c00582b800858700160ae002c09c004a242a2430543058320c30542278305422743054305432403240305432383010227c227c30543054301030103010321c2640324832482128305421283054305421282128323030b82128305430b8305430b8212830b8305430b83054305430543240324030543238305430543010321c305830543054323030b8305430b83054301030b8301030583054323832383010323030b8225c305430b8323030b83c003c003c002128213c20f03c003c00285428542a0c28542a0c285420542a482a482a482a482a482a48227828542854208c285420f0205422742854208c285420f02054285420542a442a442a402a402a402a402a402270285420542a382268208c208c28b8285428b8208c285420f0205420f0225c2854205426243c003c003c003c003c003c003c002a242a242a242a242a242a243c002a202a202a202a202a203c002a1c2a1c2a1c2a1c2a1c2a1c3c002a182a183c00200000000000000000000013e2644a18ec15a24c4988111a1 else 0x94c15c007829027001988c09c0060a542a04189bc15c0060bec17001815e00202bc004253800811f001015e002047c004a19020844f001286408250c8104a1902084df001015e00202bc00408f80080af00104a512242aa24522243090aa891487c08242aa245056438a174861023512242aa2440f144880aa89140eb06286160c4227800a17d821432b06282f6045056c08a0b4151428d02213da04427e48884fc91109f9202921a0450b84f8a43404109f91c291da0450a340884fc8c142e13e2809c005056c18a14681142e13e2851a0450138008c4c04109f90e290f010427e430a434041485d02290b0105216020a0ac87142fb04283464040c8c80a175811415b02282c638412a0b0a49681142e9042851a0450ba410a174821428d02282b2085056410a1468114158082919a0450a3408a14681142e90a209501050a3408a42c04148890c290f8105056438a195831417b02282c63050a3408a1468110b790a2921a04521a020a476811428d0221990105056c18a146811428d0228086085010c10a43c04128850c290f8105056438a17486142eb02282f6045056c08a0b415142e904285d2085216c10859c2e10b382a216723842ce470859c041404e00282b20850a3408a0ac04148cd02285d60c5056c18a170881428d02208a22050ba428a027001428d022311010521a020a42c041485808285d218485543880aa87141682a285d2085216c10a47681142e90a204ba044097408a0ac04148cd02285d60c5056c18a027001087808204ba04521a020814c861485808205ca185233408a14681102310c285d214408e02084b0861096d02290ba045a0b800940f001283e002307c004a0b8008c17001281e002503c004a0b8008c17001282e002305c0040cb8008187001030e00205fc004a078008c0f001283e002307c004a07800941f001183e002503c004a07800940f001281e00202fc0040d4118949212105432425248484a490909492121086e002111c00421f80084a7001094e002505c004117800843f001085e002809c005013800a02700120e7062422e0c4839c189183831211706210fc004839c189183831087e002422e0c40c1c189073831094e00245ee0848bdc10817b82102e034245c868421f800919383122e434210dc00422780084ef001281e00208bc00421f80084bf001283e00210fc00421b8009c1f00122e7022111c00421f8009c1f001023e00202bc00405780084ef001015e00202bc00427b80084ef001228d022166a0c42cd0a89172821025d02213685448a340881e2831094e002307c00460f8008c1f001183e002311c0046238008c3f001187e002809c0050138009496811292d022525a044265490a027001404e002809c005013800a02700109e504213da0448b9410812e81122e5042451a0448a34088) else (if i<30 then 0x9c00627cc3f00189e809c006056027001889903c0062744a7001889903c00608c43700189f305c007208c1700188c809c00627cc4700182e132a086a2702204182e129c006264c2f001985d03c00605442f001982d03c006232027001988d03c007011027001a28705a04660b40f001988d03c006e0dc17001832707c0060c1c1f001823129c0060544a7001815129c0060544a7001823129c0060b84a7001e04409c00626c0af00182e129c00626c0af00182e129c00608c4df001e04009c0060b84a700189b02bc00781102700182e129c0062cd48e81189b523a04626548e811894123c00625048f001982d03c006264c17001983d03c006250c1f001891307c00660f40f00189b521a04625048700189b121c00660f40f00189c50c81060f143204189c129c0062704df0018b3307c006250477001985d03c00623842f001983d03c00660f40f0018b3307c0060a2027001983d03c006151c17001837705c006e0dc1700182f705c00781102700182e409c00608c4a7001e04409c007810027001815129c00608c4a700189a129c0060b9027001a28133a04627d027001894409c00661b40f001c1530dc00626a027001982d03c006264c17001815809c00626602700182e409c006e09416811894409c006812c1f001897409c006264c17001899809c0068a04ce81182f704a086e08417001985d03c006266027001982d03c007829c0f00183c707c006054c1f00182e129c007811027001e04009c006278c47001823311c006279447001815511c00627b40f00189ed03c00605544700189490bc00622240f00182e129c00622240f001c04409c006812c17001894809c007011027001a28707a0460b84cb831a28707a046221c1f001a04b05c007011c1f00189930bc00661740f001845409c007011c1f001c04409c007011027001c04409c007011027001828809c00613dc0f001b82703c006e0dc0f001845703c006115027001e04409c0060b84a700189d30fc00608cc3f00181550fc006274027001897129c00608c027001897129c00621a40f00181510bc0060b8c37001845707c006115027001897129c00625b40f001e0a703c007811027001896d03c00608c027001896129c00625b40f001885c09c00701102700191441560860a01020a182002a82860981020a1a89409a046a25026811a89409a04626f057001e0a409c006623027001a8810c8106a20c32041a8830a8106221027001c04409c006a1c432041a8730c8106a1cc2a041a8710a810621d027001c04409c007011027001c04409c006a19026811c04409c007011027001832321c0062af40f0018b4d03c0062d242f001894c15c0061144a7001a8710c810625043f001894809c00701102700189410dc006252027001c04409c006a19026811a86409a046a190268118 else (if i<31 then 0x6a0d40f001983303c006a1541f001a83503c007828c0f001a85503c0060fcc0f00183f303c0060af037001817c0dc00609b02f00183402ae0868dd0ab821888905c006222437001a3742ae08621e417001887c09c0068dd0ab821887505c00621940f00185006a08c68dd0ab821886505c00621540f00198910bc006624c2f001d83107c00622140f001888505c00621d417001886505c00608cc2f001885b05c00625048f001894121c00626c48700189c129c0062704df00189411dc0062c04df00189a129c006250417001d82105c006250467001888503c006622027001888b07c00611540f001888505c00625c4a7001886503c00625d417001885503c00621d417001896129c00625940f001985809c00621941700189410fc00621e027001887505c006250437001885503c006216027001885809c00621540f001894125c00625049700189e137c0062784df00189d129c0062744df00189d137c00626d40f00189b10dc0061284a7001894105c0062bc4a7001894119c00625044700189b111c006640447001897129c00626c4bf00189410bc0061284df00189b10fc00626c42f00189b10bc007829c13811e0a704e0460f04a700182b046e0c621d41f00184510fc0068a3053811886503c006114437001a28c14e04621540f00183c464e0c6620c37001889503c00622541f00189d129c00622540f00189d507c00625044f001889507c006226c1700189411dc00626c477001d83107c007608417001894507c0062bc4a700189410fc00621d41f001886b07c00723042f001885503c00621541f001897129c00621940f001887507c00625042f001885503c0062584a7001896503c00621541f001c04707c00621e027001886809c00621a027001885507c00611c17381182302ee0460980ab811886503c0060fd0ab81183c42ee04625140f00182f05ca30611540f001885503c00723042f001885503c00621540f001889b05c00760c41f001888503c00621940f001845705c0060f1c17001823129c0060544a7001823137c00626c0af00189b02bc00626c0af001823129c0060544a7001823129c0060544a7001815129c00608c4a7001815307c00608cc17001823305c006278c4f00189d313c00608cc4f00189ed03c00605544f0018b345ca0862cd146811a2e136a0868a04de81182e132a08626e40f00189b107c0061144df00182e129c00626e40f001983d03c006a0cc1f001983d03c006624c17001988d03c006240c47001985d03c00626cc2f00181510bc006252027001989809c0062320270018b3809c0062ce027001899525a046250497001894125c00660b40f001988d03c006250c47001892311c006250c3f00189230fc00627a40f00189e129c00627a40f001982d03c00627cc17001c82305c00627e02700188c80 else 0xf80101fe04409c00825802681e004c14e09c0f00203fc14e07801012a85d03c0080b84a285e004052812c0f00202951061d021014a8830e81080a602204e00410c81240f00209410f217801114a86409a0480a602204e004c0881340f002086c0881380104ca8630a810825043204e00412901102700209430f813801043604409c00814011f001850113c0060b444700189b129c00626f40f00189b907c0060b84a700182313dc0062780af00182e129c00608c4ef00189d02bc0060b84a7001825d03c00626c4a700189c02bc0062684a7001894905c0060b84a70018b202bc0060b84a700189702bc0060b84a7001a15113c006220437001887c09c00685443f001823113c006250497001894125c0060944f700182313dc0062780af00182313bc0062740af001894123c00626c487001815121c0062700af00189b11dc0060544770018b0137c0062684a7001894105c0062bc4a7001894119c00611412f00189702bc0060944b700182510bc0070ba444821c1591121470ba43c821c1590d810721a42e041889903c00612844f001e0ab05604622641f001845113c00622640f001c28c15604622640f00183c113c0070a2c1681189f923a0470c2c1c831c2813fa04627e0ac821d82905a04627e0ac821c2813fa0470bec1482189f82b010627e466811c2e13f60c70a2c1e8118b885c27c6056027001c87c0901062e21709f198990d01070ba43c82184a90f810782ac15811990c15604612a0bd811c2f31d23070a3055811c2e80920870a2c1681184a90b608760a416811c87c09010721e021831c8780860c7216021831c159112147056436041c28c1560470a2c1e811c86808608721a021821a2e510a0870ba43c821a15510a1468b94428218235112186855442851c1590d81060b944282183c510a18721a42e041888903c0070be1748c1888903c0060b8447001c28c15604622240f00183c111c007227024041c2e80920870a2c168118b390d01062ce4768118b385d21462ce146811c30b0720c760a416811c2fb052086232027001c28b07a04721f02404183c809c00662243c04198890f010721a02681198890d0106622434041a2e50ea08608d43e041c1590d81060b943a82183c50f810721a42e041c2f85d23060b843f00183c10fc006096026811c2e8092086096c16811c30b0720c70bec1482188c809c006096c1e81182510fa0470b843c85182930f010721a02681182990b01060a643404188790ba0460b8437001c2e80920870a2c1681182390b60870b84dc851c28137a0460c2c1c83182e809c006622c1f001988305c007828c0f00185430bc007a0940f00184f303c006a0940f001982303c006a17417001a82503c007828c0f00184c30bc007828c0f001831303c006618c0f001985307c006614c0f001a89503c00))) else (if i<34 then (if i<33 then 0x4105c0080944de81e00405c250417002604009a0780101189b10dc0080b84a082e00405c25041700202313660b801302004305c0080944a681e004c0801340f002054c08013801012894d03c0080b84a082e0040a7811027002604408e0f801302004307c008094c1681e004c08811c1700260400860b801017094105c00813f02004e004c08811c1700260400860b801017094105c00981102382e004c08010c1700209d12820b80104f094105c00827802681e00412822640f00209b10720780101e09b107c008624c1681e004122624c1700202510fa0780104d98790dc00826642985e00416662202700209412520780104a092907c00825049481e00412824a40f00209990a60b801049087d03c0082e017099504413c25240f00209e11101380105c02e132a088094c3681e004450a1d02681222850e813409102482305c00809443e81e00430b01102700209f11860b80105c09f311c0082de02382e004c14e0dc0f00260a706e07801305383703c0080944a681e004c0801340f00202312821b801012894d03c0080944a681e004c0801340f00202313621b80101289bd03c0080cb02204e00404a26f40f002604408e0f8010c3604009c0080944de81e004061811027002030c0801380104d815507c0082704d804e00412824640f00209412220f80104a091903c00825048c81e00412824240f00209412121780104d890903c00826c48481e004438e0d41e81221c706a0f4091c1883903c008238c3681e00416701102700203c80881380104d88e903c00826642985e0041660b8c1f00202e13660f801202283307c009829c1381e004c14e09c0f00260a704e07801011894313c00981102383e004c08010c1f00201512860f801012894d03c00981002681e00405d215027002047c08813801012894d03c0080bf02204e00405f81002700209470460b80104a382305c0080544a282e00413425240f00209a12820b80104a189409c0080b902282e00405c265027002094808813801023b82505a048e0841481e00470420a40f00203c12820b801017485409c009054c3986e00405c25102700202e132813801014894409c0082bc4a481e00402b011027002053c14e07801305383703c0080b84a183e004c08010c1f00202e12860f801012983d03c00981002183e00405a08cc4700202e128a23801012a88d03c00862302204e004050812c1f00202380c21b801014088409c008054c4404e0040530110270020298088138010c4604409c0080b84a383e00402c6210270020b380881380100ac04707c00805602885e00407821602700203f078e07801302204707c0080ff02204e00407f81002700203fc0801380110ba87c08810826642985e00404701843700204fc14e07801305383703c0080ff05381e004c08811c1f002604408e else 0xe43e04808482d21b02404242990b013409012c86c09a04809543c85d02410f21541700204f9138120210c4604809c00808c0be04808404c057024042185c0901380120b486c0901088a143604d02485121e42e81203f85182ac09043604903c00862302404e00407f21f02404242990b013409305188303c00814f05181e00409f828c0f00260a304607801018e0a303c009828c3181e004c14624c0f00260a30a607801023e0a303c009828c1981e00407f828c0f002017c1460780100ee0a303c00805f05181e00404d828c0f00202503b829c0911421dc14e048874c960a702445087705381208890ea07801044485505c0088a10ee0a7024450877053812189b0660f8010c4d82305c008624c4583e004312621c1700218930f6078010c4986705c00960c41a81e004b0620d41700248710ca07801042d82503c00825048a81e00412824441700209b120a0780104d890505c00960c41a81e00413826d41700209b11ca0780104d88e505c0082c04da81e004b0620d41700209a128a0780104d094105c0082bc4a082e00412823140f00204513225380104c89410bc00821a02282e00412821a027002086808a0b80110e60a706e04887305383702409421cc1f00221cc14e0dc0910e60a706e04812842983e004307608c1700218870660f8010c4383307c008619c1983e00430ae0cc1f002094124a0780104f89e129c0082784da81e00413622540f00209b11360b80101180e30bc0082684a088e004b0420940f002094118a078010c8088503c0081144da81e00408a2cc4df00203031101380104d885503c00826c4b094e00413625940f00200e30b0138010c7086307c00826c43c04e00413621e02700203c05e0b9c11023e0a704e048615c1182e00405e08cc4700202f04661f80101798c30bc0080bcc4404e00407825202700202c04b829c0901682b046e0c862042a83e00431061ec0f00218830ae0f801249089905c0082704a083e004b0620d40f00209c13620f80104e09b107c00826c47281e00416026c41f002582104a07801141d82105c00960841281e00408a2504170020af128a07801141d82105c00825046281e00412823141f00209410d60f801043583503c0080c811985e00410f01141f002086808a07801042c04507c00825043404e00404a08c0bb81218730ce078010c3985703c00960c41a81e00412823940f002094110a07801022894503c00862202381e00412821940f00248c10aa0780101181730bc0082584a281e004053011c0f00202502f829c09114217c14e04921c42a81e00411321d40f0020b0136a078012c1082503c00825046281e00411160d40f00209410ea1780104c89410bc00809812e0a702411360940f002583106a07801029e0a703c00813f05381e004c14e09c0f002025129a0780101709) else (if i<35 then 0x7808813801418e0a706e07801418e04009a0780141709430d2178014c3604009a0780141189b10c01380141289b507a0780144e09430d2178014c338310720780144e087808e0f801541c82305a0780140e40450660f801423e0a704e078014c4e04009a0780140a894312a0b801412894307a07801423e04009a0780144d094505a0780144d09410520780141709990a81380141782310c60b80144d088808e0b80141708840960f80141709490a81380141288730da07801417187408a0b80164440450460b80141788c30a60b801702004307a07801603e04009a0780160360400860f801544207c08813409544207c0881340940b988409607801412a0730da0780140b9868088138014590867072078014c418780881380141fe04009a07801411987c0801380144ea87c0801380140be04009a07801412817c0881340950ba86c0881340941181730b813801412a0730da0780144b18510a813801415a06c0801380140aa86c0801380140ba06c0801380140aa86c0801380140ba06c08013801419604408e0f801411a85c08013801411a85c08013801413205c08013801414887c08813801414a8810e813409514a8830c813409514a8830a813409414888409207801414888409207801414886409207801414887c088138014280b702bc0081420a889e00409560c41f00202eb0420b80105902d047c0080a412887e00404a27b40f00248911201380105b825d03c0082dc11c85e00491222402700209c13606f80104d89490bc0082c04de81e00416026c0df00209a129a0780104d094905c0082bc4a681e0040092084170020af228253801017094105c0082c812e81e00405c25041700204504621b801243887009c00921c43804e00404a25b40f00222811381380111408810fc0088a043604e00445021c42f00202510f01380105b825b05c0082684a082e0041282304170020b204b60f801059015b07c00811411888e00404621e027002023111013801011887809c00805443c04e00404a21a02700202310f013801114289c09a0488a144e04d02485122243e812025513813409114289c09a0490a243604d024450a2702681242890f21740920e60ab07604814e1460ab02411381240f00242882f82ac09214487809a0480d411e04808416e22642d82241cb0720f40905c42e13f214905e43e0480841710b84fc852185c0901380120b486c0901090a643404d02413e62643404242890f21740902548690b810905cc760ab02485121e02681241690d81202121448890fa0490a243604d02485105f05581204731982ac09214487809a04815244e04808483960e41e81241790f812021012a8890fa0488a144287d02485121b026812228510a1f40921448790ba04822242a82e00485105f05581242890f01340920e583907a04905 else (if i<36 then 0x9c00ca1e43186808813801812a86c0801340f003096128a1702004e00605262043e04409c00c0a443985c0881380181682904b82b80141482582a21f80141482502b82b801644889009a07801402483107a0780140258390620f801402482105a07801643086009a0780141709490a20b80141e0af12820b80145902311160f80141189710f60780145b82311360b80141188680801380141482511101380141482510b01380141482510d01380141482510b01380141281dc0901340941a015c09012c11414188c0901380164448580b81202160bc86c09013409603c85c0901340960b40690b81202161498990b01340960ec89c0901340961bc89c09012c11644407c0901340964448580b81202160bc86c09013409603c85c09013409614c8580860f40960ec89c09013409644407c0901340960bc86c0901340960b40690b812021614c8680860b40960ec89c0901340961bc89c09012c1160bc86c09013409603c85c0901340960b40690b81202161498890b01340961bc89c09012c1164448580b81202160b40690b81202141488790b01340941488790d01340941488790b01340961bc89c09012c1164448580b812021414185c0901380140ee0ac0e60780140be0ac0e6078014c4d83306e0b8014c4988b02e078014c49877056078014c4986b02e078014c4985b02e078014580991282178014c4d82104a07801457894104a0780145909411160f801459088b06a07801459088b06a0b80141b988808e0b801414886808a07801414885808a078014c3b833076078014c3b8330760780145b89bb04a0780145b89b10b60b80141180e30f21b80144d094110a0780144d09411020b80145789410ca078014250b31362238014c800e3110138014228b31322538014c7086306a0780140e185808e0780141489b10aa078014c458370460b8014c3b82305607801414188808e078014c41877076078014c4186b02e078014c4185b02e0780145b889b04a0780145b88550760b80145809410a20f80145809b106a07801419185808e0f801414885808a07801414885808a07801649089904a0780145809410aa07801459094b06a0780140b988808e0780140b985808e0780141489410ca078014c3185b02e0780164908950b20b80145b885b04a0780145809912821780144a08850b60f80142289912821780140b015311013801414885808a0780141289b10fa0780141289b305a0780141289410fa07801429e04009a0780141709430620b801412887307a0780145c02e12820b801427e04009a0780145c02e12820b801702004305a07801412887305a07801642e0400860b80144a485106a0b801412c0710fa0780150ea89c0881340950ea89c08813409411c8530b81380145c02e13e61f801412c0710fa07801414185808e0b80154498 else 0x64058c448530b01102383e00913a25144e04009a0841700401d91062302404409a0780200e188808e0d41983d03c01011cc2c04704a08c1681e00802f214c2e0480881340f00443291121a0360480960cf0ca4448680d81202583382c04b01c43e04809a04e0ac11c0610d812025833c3291121a0360480960ce0a00ee0a311011c0f00381cc1462202383703c00e11f05185808e09c0f00382802f828c2c04703c00e0dcc4604808811c17003c8630d01141983d03c00e0c0c4404706a0cc1f00382f90b011c1282305c00e8c94428640d81102383383204681843185c09c00e058c448630d01102700382604a81c43e04409a04e0f0c2885c090110270038500520944ee0ae0060a00a61460a113c00c12814e0ab0620f801817029c1560841700302d0530a305088e00605209411897c15c00c0a614023c1421b801814c2802b82842f00302c11021f02204e00691022203804d03c00c0ac44086c08813801a4408890d01802700304504a21c02681e00604c21c42e04409c00d01e42885009a07801829c8880f81202681304780f21702404d02607f01e42e04809a04c626c1983b02e078018c4d82305605c0f00302803a61602381e006307608c1581703c00c621c1983b02e078018c3383307605c0f00318570660ec0b81e006310e08c1581703c00c619c1182b02e078018c2b82305605c0f00302f31861602382e006051828c2c04703c00c09544e04009a0780184f89e12921541700309e31222202082e00613e2744a485505c00c274c488780820b8018c4a0490460b40f00301d51261602204e00631181202204b07c00ca264398780881380184e09bc0801141f00302313781002283e00616181202204707c00c0544a604008a0b80180a894c0801141700302e31022102282e00605e08cc3886305c00c0b843c85408a0b801817988808a08c1700303c02d81102383e006051828c4204b03c00ca20c2c04409a0780180b98830f01102700301d40f81002681e00603a81f02004d03c00c05d03e04009a07801813207c0801340f00301740f81002681e00602f214c2c0440))))))
def lvlNew11:Packing:=(2558,4,7,0,0,18,0,dataNew11)
def hashNew11 (i:Nat):Nat:=(if i<3 then (if i<1 then 0x477c39ee0000a060804db2f656a5436b92e5120c3359c5b80000c78c00000000016ba1ca48df336f9975d0f4b8f370a4000031eb9263793fb2dc522d47b2694083c8837296cb263fc33b6338000000006336a0146527a8ab0000247714eb245e39fa11b633ef231969aa527de7f6d784525f824034f59009b6bb6491b5487471f257f6bf495484f160563807c655027657bd05582278364218e02880c9e8f460368c238b1246d79d0000f236e46cb189d7d1b8d0b6503805714d1869359600008472a1955679d52d0000a4db0000b7c391fb1686417b03c47057d8e4b56de4caa5e259971584283829ad349868a1f3e1d6d70000a901d11d81f757cc7144699983cdf8d600009352c4ae000000007550e91304d5a322c7598388c5cad4530017c947b6320119a61bb54b3522b15a63fac2be755d0000e9a2a4ad0000a254958ee95f0000b034b6ab5373b054000036d000007883000010ae000067eeb8254421f0c06528f5e744b598cb72e10000c713e54fc746865b81379717891b55c4a3514715012cba1200653500030c0001440612090108000136000a132d00220711bf05230b0100191c000319004a0d06010300300326231b28005f010553040110090f068d000157011a030125051c1005142d0104662b248f580d02171609040205032d080401240000002a01151806215b03200b0501010b0a1a350b2d035e062903020019021d031208040c0608031b031c1a20022a06002141390243340025211579990b020d0304050704130f01221301000c2e00020201062c000561060103043f2c4c010620050415383c0517001c080c0c00200104000600000f050079000c302512170b014105210c02000001022d0c09170310190a0807031424070c6403000a03003c130307025f00080b370401230d0705141400030209002102060202155106013506111801021a000a0b27010d1a0719000200031e0b1e401316570201282c04140f07090c050353000102002e060101041413010b100002031e0015010b0007100c0003041b3502010b00000e1800020701291803043008293c010c020104070063051b380039000200860f032f3c060d03000c1900294400181a0522030e090005000000420b16003b05330a0a02001a060100172f004b020002080d0a002304030200070119151e0c2401011f020701000304000e001403090b2c012f1117031529071b050b021a001901000711001407040002150e01161c003300080811071703090000041400080a01050204070a2b02021b31060117075b001c062b001b01001a00203c052c120500030a030003191c02001b0502072718040a020547050d33010c0002040e0303040001000528030c35000d110000000001290000010a000001190b0103010a0503060001050d000c07030c0004050203 else (if i<2 then 0x364a503ed9b6671f147447bb0000000000000000d224002632f7943ac41016a6157ba008a3860000748f29dff6f4845088acf24d00005462656757b6c870b3ea00000000d7fd4653079563e7739060ed859f089c69c4314600005827000000006703c417f2e0b1f35001310c000063146434715800000000f4fa92c4000074e440d5087523b7519df90400000000e55662b200000000b4c0e250c3e20000f2f068c9c2d200000660000099d1b09fd07a0000000000000000000094c7373e00000000601c0000979ed2b1641d00006857c698f3bc70820000d4f90000a0fdd65dd8d740e300000000000051a492f500000000a1cf53f70000f8130000628403b593152771312da7c440bd0000c8a200000000d2fba1320000b60ce041e15135d70000a7dbe86558810605e6b9608d52a80000391254f6747852419327299c87999174b8fe0000a57700000000b5aa539202fe0000564953d93652d249f38c433278d5377a0000560f06efc2d1b165441f627a0000e762f49782b6000039a3000000000000000000008065f4c81816706b0000b3a879b3181a00008506a90f752055db146767f1b5b30000e17ec4990000312c0000b94f53f8b25c418124b409fc77920000b58f00007116703875a16440c93878e225a600009363b09770bfc42bb4eea39d0000e04912e3441a72157989e09446c9000025ad04e00000564e275800006958000011750000c3de000080530000f271b3a770b6467c5374f2d798b200000000c66fe7f257783081f29fd3e50000330785ef306ee5ebd0110000000050fb0000279a188800000000a3dc603cd4f49741845643a3250e32d902ad1974d26744337298e70893ba1927954229ea06eaa169e60157cdd1a500001685222f705a0000722bb0e8a573913fa32ec170a51e433ac9b764a80000770c937c34365337528fd59c816856aa000075a8213650e2c67115f441d66173d80ae0bec5bb995ab54168a3a149c4e1921ad9217366c986f1df65b6b5ce82107021129b39d5f1c249def97cf1bda2d4135e0000b9fd8503b52300001625c40326d8f4a67015d394f77519d861b31982a4f3524b576e940d87aff871d441274956e340fca55158bc0000197d81a8e1ea46a0434618a5318ed6064176487606dbe3b2d849e81080a507407407b3c2757a0780961ae06682a2e96a32caf09d2802a6fbf479903b384a737dd2c7d9030000762e81f5000004af89e9460ae72203ca60dc20c9e93ba78807a3000070e0000081d3f93d58ca000078548826373fc8ed160b132a00002156239e63f100006949275008b98923484d06890000e7a431080000890816d3b413b55516361295890c552647e50000572e00004673000012200000c680c85b5800602d22bd756f0000000066cd011b66b7000075d23782f4a3997a30d1a029 else 0x224cb005000011c11842e6099043d34100000000314aa141f3cf0000f1b0f438057f0000602b19a9730c82370752e84ee4d2638065a00000d63a2128d7eca9d4c0d900000000d4d60000c3a6535681b93996000025d638780000000002b8799489c926a1347377390000586871e8b57129240000000068bfc0fe8133600712a0c81ed688f2b7000055b90000664c00000000b145892c934e0000f12453a20000322e5769d8c1b2c8000037ea0000000057b02361f968849d24c466a8107b0000a06a0000d8b32207000043f50000676aa8ee071991b470f7f8449619709880cd47d5091ce79c029d3093a515a37be26652830918822a1376c5d347e68365f29cb3d8b46d9117039c6018030320b148efb9ab91ced43dd843f44b9106e292859131daa11480950753d310a5c5e9ca07eb57a9398a11ba3585742400000000624ad90a00003323d5e6948591aa0111f5a30786b1476422000091e2595100009134b9b09305000021dc441e00000000000000000000939792d0d2ccf1be0000d9d3a1e9000067300000b18606d41486a2148326e425000000004804e6404113170761f22620258996bc54705576040571b2902e60a200008179a88949410000664453432230628e61a1b0f1b22c000000000000f43f786cb5c39046869c05aef4d1000009780000c579b052f00f3837d7d20000875d12e667ca000094a7533087654563f1b579350000514ed5b4a17fd3ae000092a130db84dc5793d26f0000000009a0b830c9af4858e944b0d4d6b10000000029db507088bbf55e0510908e0000d5906457f15b159746ada32c00000000c0b4d8ce283dc4b270cc100cc1fe0000c6b06192517ae94c43585993d0dd780b91c98658000004a1372a8646b00b105cd80322dbf061124447091118c36cd85c05b72349e086f7607697598db07428ddf2ae958be2ce2331025544fe245c000086e168203952b4d9476d51d975e997e376a737d48811c423e40277de0000236055ec000001d8170e15fad8b8e8a4e72f0448678ee96df44ea6d915f80000b099b48e84b154430000f611925900000109d51bf639c8e70000b47e991d00000000f4836444313d100ec48bc4420000d42ea587a9579914a74a000000000000e917000090372177000007f5a5c800000000d47a9970b9bc00001142214f0000144a2084f59360761239649537020000c7d9c1e393c57969c7238509484722cf77d0000000000000b4b9e321000033d200001862d71213ed573a782243d6e626371037ae0000e81bf9d2000000000000c04200000735d8fa89a40000650b983b07ed36750000d633e6c224474890c33456f075ccc0c8204a786138a707cb4232556ba9606959000000000000048800000000e27f0000b4acc7ce58af2016392a19dae0b926b5c24f44e9a306e965c553)) else (if i<5 then (if i<4 then 0x1737f74e62bbe40800005459d198975b51d50000a4b3e98f95d90000b99b0000f637700af9c17013e449465f910764eae2cb640e16e44661964fb977e4e653895628f5df0000609cc98e3294f29e2148163e70cad1c38064492d4666929794ba00001085000000000000000071c09537b1b8719e65523582b159132da806015085070000025200005225f19624a900009492000000007781b82f728d0000f4c1d0f20000c07dc2c034b736f100000000c7e7c103b56ea3ebc42d19cf2665323ef2de59720000000084bdb45fc6f9000000000000b8ccd6fea112564d0000f8d8b00d000087dc3809c4cf0000d87e4621e5a40000000083e9965ed45537a0000000000000000034760000b5dc87d8b61739b500000000e229c2b570c20000335f08da00000000273856917282f57c950d656ac6f300004720d2930000e70657e0f56600000000000001de000013f3c14bf2eb74fbb6540000606f000002770000000038d1b8b75490858db0ee642687290798000053f90000167058c5a90ef406e1ee000056edb41bd4fd69f6000095fb48f1f32083b800c556c5277d17fb620ba88f214c78931055b2ef36ba000000000000093a53fb0000f10567ef571e038dd4a449f460a9930d42b3b855e419b364954c89e3682e00000000d38a420000001622e2dde7df0000d8fcc557000068ea97d346cfa22254f20000000044cd0000d52b000075e16398000094f7f598373631e1e8eb7772819365de00000000210da0ff45da5569894d0000b814853a00008184000000008489820f470d0000499df7c59003209674b0813c000011a259edd07723ec145bf31de763532800003429c1d20000c30030270000c0bb000039ccf94257895500b80ff60e71d15887d7fcc022a1ac000095ab090700000000374400008578e9451662d6870000071a8190000066ca034a9469a64761c61933d308000056080000a62f000072b4242c817d00000000369660eaf13b15ea23c30000000069d7980c35c1c61850a8e8fd95b1121273700000a81887b1268fd6d631c500000000847c925d41d7a37940ac113e0000000065dd0000a8a9c9ac0000570a3430d0484464426d25f694dd0000d9c8809b0594741ca821174ce7f870ebf89427d6f6b3e2f93188000048ad0000c9cd87da3123000000008514b8f800000000000052a300007504000064dee07839f1507c7711679fe5bc8607e2477592e01d87aa116426dc854da4014087d27e19c521f8d21f83c7d4bbb2686264a1faf325e3ddf8cf90da683a99b9a9363219c0e4a79672d5b131c72c521d063d7543e681f6821990a75f501963eec84851808627f0922624413540e1238135c2b59de03fa8c00000f773000000000000716f000086cec41424870000000015bdc01206deb23d851f90e9421732bc0000954792e9 else 0x89dcc7a8671c000009ce41bc0000e39ac6eec8e1c8b5908b73d5660d469a0000c49b933cd15c0000c411b0bc00000000d269536e866a000031db99a7292ea4810000e1e70000000000000000d088b819e87b4899000000000000b5d1753859f300000000a981e2fdc3b4456413a130500000170575ba3494d1ade0aac2fa0000140ce783d956d6b827c926b20000d4df000000000000426591cd000000008747000000000000c6993764c6350000e368b1670000f84c0000d531999f45e8503378c2d939000028def234918f521c000030fac4da46a3f49f000000000000b378a78d8115d656d85e0000c672000010a6d46e18b1835067fe58bec248296bf39988c303cb219f833579a5947ba8e5785ae54626a466a2f8aed8ec394bb961738f418737e125f3f874000084fca063917c99f2734538360000277760450000127236e6b16652a967b30651b65af3b0a9e00000000027ad4071e6df966e18f9d54081fff10bb5253484d3f2967b3418d72d54d8623846c35834b5ff4072793ee973903534e3a76b416cf50ab4d7d72b50792511468b2211157500f3861429cba0ef725b074db8b6a8c7c468246ff67ff32b87ff82ec19e5526b8963b76779ae82e223a5d4ce976f11214206859975cf037531cb0000605b37c06451b9b1b95ba911158100000000e897f7b5000097a1f9e160de3431c6af716d93df000047f4998bc216983c004cc91f0517443be4f8f3af67a705d8000032091130f12ec172f20d6185202fa64b296600001020c7c7f3da2227b13a6841e4d364c6000020e589c00000834797d7034b27700000479b00000000b4ecc4cbd062a22850f866ae974263550000910f000000000000a0cef7fa0000e623030b0000000000000000000000000000000000000000000075b200000000000071624213c9e475ac52790000649e289d00000000b7e40000b143930a627bf4e8000092ed37a568501718586798f470394595a34dd1ef04200000f19c908c907377f3333fe15261f4710129193879c9eff0a0144660b3a6d1e5afb1dd0000835c3866e43c8475c61200000000c2e4a83919bb955a45830231f28bf11e0000a36de724483eb6777929594603160000029999f8f243a884163c007e327c720a9794386a229a368e720399e6c0d3c90b961696e83561b3ab97b7d68319eca78f69793463887380f5f288f3c1d3cc8634c73b2104b4587690b4ed25f998ba9324192fd2afb5e0b70b398416da96d2d55f8852a2c5749ac40952d616b493959051f18a715e11f143a0a6e9577b434406dd91a628a83603850cc535338422cdd87f38aac85fc312a5b5305e5140e287758c22ba0000b5f5c89e201f6362e11f71a3380d19f5045d331c199281e6937a08e8e25697b829950533a0d20000043e00009428861010680006e9480000a6f6) else (if i<6 then 0x94006549e69f62753226134fa7bce52cc1533565615428f689a6241608a60270a3b9312a10b5a439f31b0000e10225bf837ec7c201a083290000b0c1c3e605020000966b039f78a07754686f368df4c92641823fa5be000000006630374f331f20cb96b6d5f78787253ce6ebd817899ab89178f500000000867a208300000000e0d68631797ff8d9797b934c00000032937f2391000000000000421833572928d18b79eb59c6f95d528530abd51a000014efc831662a34b8b1c790440000f54eb835c5cdb6fc935bc1f0a8e982c673e0138534aa051600000000987250e604a502f213f0c66c00d70202103139dd5570a78ad885e860a9057160573c0221015d04547755520e21edc6e045f0433e620560f676921916b36917aca82cb1fda8b0d95c177f10d0057d088a973d0000d6fa49430000603de6ac60b0a45a44e2000060a70000e01a769ba3187962680877a23725830ff4b67906632f00008445c7660000000063ce000000001432344f411096c4e61e482806d522450000d768342f22010058a9c7f2f8000085b0e2f1e6fd96bd26a925e3d9bd64abc86d19b2a03ab4ff723a000088330000b33d78950280e19100000242e9260000445266485025974b0000a60229919223f0c417c1b9321856b785c8cda6942733e0f03934000036e5588b3067775a553200006199a1c8f62cb5f19864761c058ac898f28600000000781da920d21e36c60000c8f2e8dbc812625e066493bb516e6580667ef19a0000d1827731c2eaa48a937167dda393735300c3a262a59a77915183f1bf03c9153d73d330f978f7b2c27089455c7383a88d0000a2c156151091703045fe804b0801163bd0b70000a47d000030b2270f89b400003377284f25180000271b48b4023551380000891a36760000812bb21b81e033f60000c56c1251e100796e70362524b35418d226ff00004404265c082925fd6339e9bed5c9889fa129000033b30000e54a899ed971e3f400000000000067cf000023173126c48c17a60000e62bc7f918bd3204e2600000a859753f077ee2fc428909a1e38ee9e7a588000000008281580e00005505c7ab590962a614d4153e00000000164327f016c07761d68a77c60000e69ed81f942a64e50000d604586b0000000090d8540a8002151dc44c0000598893ac1302b5604701006978e603e4050f64e70000f52ea8d4b7261562b3c02877e333078b696f004f00000000000000006910b0c6e745000012f495c00000a28a00005178000062aa0000530459c213d13482226e582b16e70000d01e5700000000004466881c7774838231a993fd46e2000012d8d40b17150000d0c730a3000078462125e52fc3ff0000b028c2530000c367e3db1900c4c50000249344610000c55b72ac0000b6f8b0aff5cb8756b98ca66390ad00000000518cd4a0 else 0x73d445290000000000000000083230e7000000000000784500000000416ab693423c000089d0e8c400005161a258e89684d0f9fbe9d6436ab586e613000041b1f5215902a84016c1a85141e4f8fba3fec2610000d2bfb25a4721000057e2682a451c889a72a5b4a2a023c88c00000000d09a0000e87c0000888626bea2ee6815f69db1d48387575c210a471db5c7000000000311d8230000b26a0000a74876f7e530688e00005757362d02c9e080267d09503659a49cd964000055f2d5c6f0ecb91e12335983000067760000443512e70000902a44f06090d6f50000173415edc8530000694a230927140000b87d34c396ec895e309e4296a9d90000b1ae335d42b9a84b91ab507fc35a0000000000004163d629397ee5a2947fe2ff00000000031e0000696cb2dfe86ed5ee0000872823d0b4bf0000000049370000d059348070b8c3aab61ff8e30000066d000049c3e3c6b985e93c429197bf295500006194e7c80000153925a70340a6682437c8dcb01bb7e8d967e5086568344dd87a80ba41bb115ff08ff273959ee8c65674f559f3d7890dd732157e848d228cb2d3e0cf4513363899bf0000a2c3331a3779982d005df7ba3010000000009980a53456780000206d524ea7973600e27419ba95a583ad35a987b9d6c72075a1203122f8d3c59b0000e2da0704b645639b00000000b51233b600000000000093a9476c166749315501030e10a1189bd4272572d695d3b119f743fc1574661de915a0df585d06f2604745191024c92bc8240000c41297b4f892352a554587f719e252a4000088c8c1b70000b1a72922a313326c883f0000000000007197c9a8975e74bc99b8000055d0a1550000e2b0c00451fc00000000d751a171405f754400000000208ab15700000000b669823b694e76cc62a77998d72723e3f657a4bec1390000393000009925453b15e46040446500000000371600000000a5e50000b7431301f68482e842f3a7be94c2c496e1aff1cc88f0000071e5b396a2ab64cc000000000000995323bfc1d0f4150000a3be3290b5fc00005882f11cf3bd4554912f0000c8630000e790318dc9f981c405d59976d11a802ce46b298717e9b127546a8342b1f656c82536f8ff204ec1f9f1ec33a4000049f00000000083e8706c0000840f00003348410e05d4c208e19b)))
def lookupNew11:=lookupWord 640 3174 8 16 12 0 hashNew11
def dataNew12 (i:Nat):Nat:=(if i<3 then (if i<1 then 0x69f929b1e96aa92368dc2894e850280b67c6a781e73d26f866b3a66ee62ca5ea65a82565e523a4e1649f245ce41aa3d863962353e31422d46294a254e21521d56195a155e11620d66099205be01e9fe15fa41f66df299eec5eaf1e71de349df75dba1d7cdd3f9d025cc51c87dc4a9c0d5bd01b92db559b1adae01aa55a6a9a2fd9f519ba597f9944d90a18cf58949859d81f17e457a9976ed73416f956be9683d64b961355db15a2d56a953254fa14c1d4899451541913e0d3a89370533812ffd2c7928f5257121ed1e691ae51761140510a90d4d09f106950338ffdcfc80f924f5c8f26cef38ec04e8d0e59ce290df84dc78d96cd688d3a4d0c0cddccaf8c814c530c24cbf90bcd4ba18b75cb4a0b1e4af28ac94aa00a67ca2f89f749c1898bc956092048ea88b4c87f0849481387ddc7aa877747440710c6dd86aa46770643c61085dd45aa0576c543851044df84aec47e044d441c83ebc3bb038a43598328c2f802c74299026ac23c820e41e001b1c186015a412e8102c0d980b04089806540438021c0003ffa883ffe954fffa551ffe8887ff9816ffe484bffa882ffea207ffa552ffe888fffa113ffe844bff9522ffe485bffa556ffe8ccbffa331ffe889bff9856ffe60dbff9716ffe549bff9516ffe5447ff9316ffe4c4fffa336ffe61dbff9826ffe604fff9761ffe5cdbff9651ffe54cfff9523ffe4c9bff9a76ffe6187ff9853ffe608bff9812ffe6047ff9762ffe5d5bff9732ffe5c9bff9713ffe5c4bff9653ffe58c7ff9623ffe5887ff9536ffe5487ff9513ffe484fff9211ffe214fff8851ffe689bff9873ffe61cbff9852ffe6147ff9832ffe60c7ff9823ffe5d8fff9752ffe5cc7ff9711ffe594bff9622ffe544bff9323ffe4c8bff9321ffe4c47ff8852ffe14dbff9a56ffe61c7ff9863ffe618bff9833ffe6087ff9753ffe5d47ff9733ffe5c8fff9721ffe58cfff9632ffe584fff9612ffe54cbff9531ffe4c4bff8a82ffe2087ff8531ffe149bff8326ffe6a1bff9a36ffe20cbff8831ffe208fff8532ffe148fff8521ffe144bff8321ffe084fff8813ffe204bff8513ffe0c4bffaaa2ffe69c7ff9a21ffe294bff9a83ffe6a07ff9a73ffe69cbff9a51ffe688fff9a12ffe28cbff9a63ffe698bff9a53ffe694bff9a32ffe68c7ff9a13ffe6a0bff8a12f7e9dc7ff2111bfe69daffaaa1efea21bbfa881f7e9ddbefa661fde9547fda331ffa888bfea221ffc845affaaa2f7e9dcfdfa772fbe998fefa662fde955bfda336ff68ccffea226ffc844aff9a71bfe695aff9a26fbe595affaaa3efea20fbfa882fde954ff7a552ff68ccbfea223ffc844eff9a73bfe69caff9a16bfe684aff9a86bfe6a06ff9a52bfe6946ff9a36fbe58daff9a83bfe6a0aff9a23fbe585aff9a53bfe684fff1511ffa484bfd9533ffa548bfd9313 else (if i<2 then 0x7a198521604e0e83a0a02e0681e0300602a1e04647414449104390c42c080270641f044170240f018030148a19063a0aa2688a1e07a1a858118320f82a0b81a0780c0180a094c811d055134450f4340d42c08c1907c1505c0d03c0600c052286498c82a89a228781e86a1604e0e8360882e0681e03006028c951cc641544d1143d0d0350b0270741b044170340f018030148ba92a320aa258822287a1a8581383a0e8280b81a0780c0180a45d49519055134430e43d0d42c09c1d0741405c0d03c0600c050280960aa268821c07a1a8581004e0e83e0a82e0681e03006029175254641544d1143b0c4350b0270741d050170340f018030140f28e82a89a2287a1a066148581383a0f82a0b81a0780c0180a16618136c831d46414449104390d42c08c1f044170240f018050b806894a4990a320a2258821c8621604e0c83a0b8120780c0285c05e4a524c7519051124410ec310b0270641d05c0903c060142e02e06894249902320a625882228581004e0c8200b81e0300a05012c14449104390c42c080270641f044170240f018030138a20a62489a228781e86a1604e0e83e0a82e0681e0300602747414c49134450f4340d42c09c1d07c1505c0d03c0600c04e2882a8962088a1e07a1a8581383a0f82a0b81a0780c01809d1d05512c411143d0d0350b0270741f054170340f01803013a3a0aa268861c87a1a06a1604e0e83e0a82e0681e030060271441544d1143c0ec310d42c09c1d07c1505c0d03c0600c04e2882a89a228781e866148581383a0f82a0b81a0780c018099660e136c831d051124450e4310b02307c1105c0903c060131289b6408e03a0a2248821e862160460f8220b8120780c026171294911806414449104390cc2c09c19074170240f01804c3c05a8e6320a2248821e8661604e0c83e0882e0481e030099284902546414c49104390c42c09c19074170240f0180483764a8c829892208721a858138320f8220b8120780c024193214741444b1043d0c42c09c1907c1105c0903c0601211590a320a2258821c86a1604e0c83e0882e0481e030091704a5254641444910c390c42c09c19074170240f018048b80b8942488c8298961c87a16040138320802e0780c0240eb25053124450e4310b0270641f044170240f01804592a3a0a6248821e8621604e0c83e0882e0481e0300882ec74144491143b0c42c09c1907c1105c0903c060110b8942488c0320a62585216040138320802e0780c022c841444b114390c42c09c1907c1105c0903c060106320a22488a1c8661604e0c83e0882e0481e0300808a1702ac8414c411002c0802707c1703c0600f0f0166320a019852160401383e0b81e03007050c8414c411003c0802707c1703c0600d0c990829882200681004e0f82e0780c01a143190500ec290b02009c1f05c0f01803 else 0x2a1e31d05512c411143b0c4340a42c0802506c1d04c1502c0f0180543c6418c82a8962088a1e066148581004a0d83a0982a0581e0300a878c741544d10c390ec310d0290b0200941b074130540b03c060150a58e6320aa268881d8621985216040128360e8260a8160780c02a14b190531244d1103d0cc290b0200941b074130540b03c060140f18c8298922688a1e066148581004a0d83a0982a0581e0300a320c641544b104440f4330a42c0802506c1d04c1502c0f0180503c6320aa268861c8781985216040128360e8260a8160780c0281e04647414c4b10c390cc2c0802706c1f04c1702c0f01804c300b8156418e829896218761a0581183e0982e0581e030098781702c0ac14c4b10c3b0d02c09c1b07c1305c0b03c060130f023279908298861e06616040138360f8260b8160780c0261404a0ec14c4b1103b0cc2c09c1b07c1305c0b03c060120dc2e0560a6258861d8681604e0d83e0982e0581e030090500e320c7414c4b1103b0cc2c08c1f04c1702c0f0180484a6408e03a0a6258861e066160460f8260b8160780c0242285c0ac14c4b10c3b0d02c09c1b07c1305c0b03c060120a02505e0a6258881d8661604e0d83e0982e0581e030090781182d05312c430f0330b02706c1f04c1702c0f0180484a0f0232760a61e06616040138360f8260b8160780c02414324c6414c4b1103b0cc2c09c1b06c1702c0f0180442f6498c8298962187819858138360d82e0581e0300885012c14c4b1103b0cc2c09c1b07c1305c0b03c060110c8238298962187819858138360f8260b8160780c0221182f05312c430f0330b02706c1f04c1702c0f0180442e0560a6258861d8681604e0d83e0982e0581e0300885012c14c4b1103b0cc2c09c1b07c1305c0b03c0601108e0a6258861e0661604e0d83e0982e0581e0300809411b190540cc2c0802706c1f04c1702c0f0180422e8559063a8c82a89a2287a1a858160460c83e0a82e0681e0300602c228780a919055134450f4310a02c080270741f054170340f018030162e0b325292244116418ea320a2248821c862160460e82e0481e0300b08a1e02a46414449104390c42c080270641f044170240f018030158b89f24a8c8298922688a1e86a1604e0e83a0a02e0681e0300602b1742b46414c49134450f4350b02c09c1d07c1505c0d03c0600c0562ea499063a8c82a89a2287a1a858118320e8280b81a0780c0180a85d0ab244641544d1143d0d42c0b0270741b044170340f018030158ba15a320aa258822287a1a8581604e0e83e0a82e0681e0300602b1742b4641544d10c390f4350b02c09c1d07c1505c0d03c0600c0543c08c8e82a89a228721806a160401383a0f82a0b81a0780c0180ac5d0ad19055134450ec310d42c0b0270741f054170340f018030150b899a488c82a89a228)) else (if i<5 then (if i<4 then 0x8581004a0d83a0982a0581e0300b84a0bc1544b13443104380ec310d42b0b0200941b074130540b03c0601708c1723a0aa2589a218821c8601a85616040128360e8260a8160780c02e4b82b05512c4d10c430e43b0c4340a42c0802506c1d04c1502c0f01805c260548c82a896268862087a19862140581004a0d83a0982a0581e0300bb24c8414c4912c411143b0f0310d42b0b0200941b074130540b03c060172519082a896208861c87a1986a158581004a0d83a0a0220a8160780c02e1713e0d1324a52546414c4b10c3b0cc2c09c1b0741405c0b03c0601626c1582889a2188a1d87a1986814858100460c83a0982a0581e0300b3244941444d10c440e43d0cc350ac2c0802506c1b0441502c0f0180599224a0a226886228761e0621a85616040128360d8220a8160780c02c1283b05113443104380f4330d42b0b0200941b074130540b03c060160560a62489a2188a1d87618868148581004a0d83a0982a0581e0300b3204841544b124440e43d0cc350ac2c080230641d04c1502c0f018059902420aa25892228761e8661a05216040118320e8260a8160780c02c0e41544b13443104380f4330d42b0b02008c19074130540b03c060166388e82a89626886220721c86a15858100460c83a0982a0581e0300b31c4741544b134431143b0e4340a42c080230641d04c1502c0f0180584782a89626886208701e8661a85616040128360d8220a8160780c02c1192905512c4d10c410f0310d42b0b0200941b06c110540b03c060166308c82a89626886220721e866188581004a0d8360882a0581e0300b3184641544b134431143b0f0310c42c0802506c1b0441502c0f0180582382a89625882218721e0621a85616040128360e8260a8160780c02c0ac1544b12c4110c390f4330d0290b0200941b074130540b03c0601608e0aa2589a218861c87818866148581004a0d83a0982a0581e0300b0941e0464f13ac9414c4b10c3c0cc2c0802706c1f04c1702c0f0180583c6498e8298922688a1d8621a05216040128360e8260a8160780c02c22b2105512c4110c390f4330d0290b0200941b074130540b03c060162518e82a8962088a1d8621a85616040128360e8280882a0581e0300b128c741544d10c390ec310d42b0b0200941b074140441502c0f0180582e2649424812a320a6258861d8661604e0d83a0a02e0581e0300a85c4f9324a52546414c4b10c3b0cc2c09c1b0741405c0b03c0601564a0a62489a218721e0621a85616040128360e8260a8160780c02ac9414c49134430e43d0cc340a42c0802506c1d04c1502c0f0180559263a0a62489a220761886a158581004a0d83a0982a0581e0300ab2105512c4110c390f0310d42b0b0200941b074130540b03c060150a58e82a896208881d8621a85616040128360e8260a8160780c else 0x6160401383a0d83a0982a0581e0300c1705b8470531244d10c450ec3c0c4330a42c0802506c1d04c1502c0f018060370d0152320a226886228761e8661885016040128360e8260a8160780c030c89224741544b134431143b0f0310d42b0b02008c1906c110540b03c06018251902420aa25892228761e8661a85616040118320e8280882a0581e0300c0464e1364741544b134431043c0c4350ac2c080230641d04c1502c0f018060946388e82a89626886228761c86a15858100460c83a0a0220a8160780c030580501293705512c4d10c440e43d0cc310b02008c19074130540b03c060182c02326c8e82a89626886228761e06218858100460c83a0982a0581e0300c050129344a41544b124440e43d0cc350ac2c0802506c1b0441502c0f0180602e054942320aa2589a218821e8661a05216040128360d8220a8160780c030578501292905512c4d10c440e4390d42b0b0200941b06c110540b03c060180b8152508c82a89626886228761c868148581004a0d8360882a0581e0300c05c4a41544b12c4110c390f4330d42b0b0200941b074140441502c0f018060b32c81582a89625882228761d8621a05216040128360e8260a8160780c0302285012c1544b12c41110390f4330cc290b0200941b074130540b03c060180a02525a0aa2589a218881c87618866148581004a0d83a0982a0581e0300c0780b02a4641544b134431143b0e4310a02c0802506c1d04c1502c0f018060296499082989225882220721e8661a85616040128360e8260a8160780c03022b24c8414c4912c411143b0f4330d0290b0200941b074130540b03c060180bc2e27c9925292a308c8298962187619858138360e8280b8160780c02e1404a4dc1444d10c440e43d0cc350ac2c080230641d04c1502c0f01805c2326c8e82889a2188a1d8781886a15858100460c83a0982a0581e0300b8464f414c4912c411143b0f0310d42b0b0200941b074130540b03c060172781582989225882228761e8661a05216040128360e8260a8160780c02e1193b0531244d10c430e43c0c4350ac2c0802506c1d04c1502c0f01805c9d0560a62489a218861c87a19868148581004a0d83a0982a0581e0300b85012c14c4913443110390ec310d42b0b0200941b074130540b03c060176449182a89626886220721e8661a85616040118320d8220a8160780c02ec81204741544b124450ec3c0c4350ac2c080230641d04c1502c0f01805c9c26c1582a896268862087a1986814858100460c83a0982a0581e0300b8604641544b134431143b0f4330c4280b02008c19074130540b03c0601708c9a2520aa25892228761e0621a85616040128360d8220a8160780c02e1791d05512c4d10c450ec390c0350ac2c0802506c1b0441502c0f01805c4508e0aa258962088a1d8781886614) else (if i<6 then 0x12c411143b0f4340c4350ac2c080270741b07c1504c170340b03c0601b0a02563a0aa2589a218881c8761886a158581004e0e8360f82a0982e068160780c0361404ac641544b13443110390f4330cc290b02009c1d06c1f0541305c0d02c0f01806c3c08d8c82a89626886228761e06219852160401383a0d83e0a8260b81a0581e0300d864158464741544b124450ec390c0350ac2c080270741b07c1504c170340b03c0601b0b899258942320aa2589a2188a1d87618866148581004a0d83a0a0220a8160780c0361732105512c4b104450ec3d0cc350ac2c080270741b07414044170340b03c0601a08e0aa2589a218861c87a1a0621a856160401383a0d83e0a8260b81a0581e0300d02b05512c4d10c430e43d0cc350b0290b02009c1d06c1f0541305c0d02c0f0180682e63a0aa2589a2188a1d8761886a158581004e0e8360e8280882e068160780c0341713c4a1250531244b104450ec3d0cc350ac2c0802506c1d050110540b03c0601a0b89d2509282989226886218721e8661a85616040128360e8280882a0581e0300d05c4d9324a11905512c4d10c450ec3d0cc310b02008c19074140441502c0f018068b32c82e2520aa258962088a1d8761886a158581004a0d83a0a0220a8160780c034171324a11905512c4b104450ec3d0cc330a42c0802506c1d050110540b03c0601a114152320aa25892228761e86618850160401383a0d83e0a8260b81a0581e0300d05c4c9284641544b1344310c390f4330cc290b0200941b074140441502c0f018068260960aa2589a218821c07a19866148581004e0e8360f82a0982e068160780c0341741544b1344310c390f4330d42b0b02009c1d06c1d0501105c0d02c0f0180642e26c9424a0a226886228761e8661a85616040118320e8280882a0581e0300c85c4a1250531244d10c450ec3b0c4350ac2c0802506c1d050110540b03c060192e0b70a02582989226886220721e8661985216040128360e8260a8160780c032173224891905512c4d10c450ec3d0cc340a42c080230641b0441502c0f0180642e2709b2520aa2589a218821e8661a85616040118320e8280882a0581e0300c85c4d02a4a11905512c491143b0f4330d0290b0200941b06c110540b03c060190b02582a896248821c07a1986a158581004e0e8360f82a0982e068160780c032599641404b05512c4b104440e43b0c4350ac2c0802506c1d04c1502c0f0180642e25c9482a89626886218721d8621a85616040128360e8280882a0581e0300c85c4f9324a52448822c831d46414c4b10c3b0cc2c08c1d0501702c0f0180602e648922320a226886228761e8661a05216040128360d8220a8160780c0301404a4f414c4912c41110390f4330d42b0b0200941b074130540b03c060180d42323a0a226886228761c8601a85 else 0x5012b250531244d10c450f0390f4330d42b0b02009c1d06c1f0541305c0d02c0f018070280959082a89625882228781c87a1986a158581004e0e8360f82a0982e068160780c0382282ac841544b12c411143b0f4330d42c0a42c080270741b07c1504c170340b03c0601c0f01563a0aa2589a2188a1d8761886a16052160401383a0d83e0a8260b81a0581e0300e170171324a12446414c49134431143b0f4330cc290b0200941b074140441502c0f0180703c08c1623a0aa2589a2188a1d87218066148581004e0e8360f82a0982e068160780c03811b250531244d10c450ec3d0d0310d42b0b02009c1d06c1f0541305c0d02c0f01806c1564a0a62489a2188a1d87a1986a16052160401383a0d83e0a8260b81a0581e0300d846c841544b)))
def lvlNew12:Packing:=(195,3,7,0,0,16,0,dataNew12)
def hashNew12 (i:Nat):Nat:=0x6da00000025f28a00018e4388000cbc2f000000403919f60fc70000000005d6ad2a9e2dd00072eec7dcf93600022d8508000000007aaba6e3c0003b18005bd400e4d18de50000000095a050004bf2c6f810002021bb80074cc2a10fd0d1db10ac90b25f4f0000002bb5b5ea4d8400000300000061939d00000030e9a2000720738000561212c9a3c48a8800521000285eac00000010809899f2115102b780059b0006250de28b132f3a28cd549a3a59bceeae000386bc08001ddd536ad6540447b9c28114cd569ccb25ace1ad4a94d81dea605aa9fe5860c5b4f17808c947a7dc03a9049093b87a9ee567d8d926d7c806ce0b0f3559bed1b3ff166818b04130c585c984b55e2ba36a02acb6c3ec61bae16a423bdecc51873745efb380055719523c800359611b41fd20003bea340000005455ca58600000000018bfa28002c10004dfcd10002afb3300044880061c0001a74a3149a9700025c5877d3a3e0007094242480000000000000430002b90000005298003e00000005db8000000000000003ab58f0003c2a89e208004b1721810b3130642481a0283c50c4f0c1356e044851c000810ba8080003021c00684012800009023c00c0848480
def lookupNew12:=lookupWord 49 266 7 12 8 0 hashNew12
def dataNew13 (i:Nat):Nat:=0xb82a8c052251087432140a04c1a0f0482c0a07010098b9248c05225108743214098341a08058140e020121402912884381d0c850260d078241605038080451c0a44a210e8603214098341e09058140e02011f1cf13c00ffc3ff9bff1ffe2
def lvlNew13:Packing:=(4,2,7,0,0,9,0,dataNew13)
def hashNew13 (i:Nat):Nat:=0xf402000006d2
def lookupNew13:=lookupWord 1 8 0 6 2 0 hashNew13
def extraCols:z1 ColumnInfo:=[(0,0,511,0,15),(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(3,0,508,0,9),(6,0,505,0,9),(12,0,499,0,9),(8,16,486,1,9),(2,64,189,256,9),(96,0,415,0,9),(4,128,347,32,9),(136,0,375,0,9),(264,0,247,0,9),(288,0,223,0,9),(256,64,189,2,9),(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8),(5,0,506,0,8),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(19,0,492,0,8),(25,0,486,0,8),(9,16,486,0,8),(0,32,94,385,8),(36,0,347,0,8),(40,0,471,0,8),(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8),(134,0,377,0,8),(140,0,371,0,8),(164,0,347,0,8),(36,128,347,0,8),(258,0,189,0,8),(260,0,251,0,8),(280,0,231,0,8),(322,0,189,0,8),(258,64,189,0,8),(2,1,460,48,7),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(16,1,460,34,7),(16,4,353,138,7),(21,0,490,0,7),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(56,0,455,0,7),(74,0,437,0,7),(83,0,428,0,7),(128,1,332,50,7),(133,0,378,0,7),(128,8,99,276,7),(198,0,313,0,7),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(273,0,238,0,7),(256,32,94,129,7),(32,256,151,72,7),(296,0,215,0,7),(324,0,187,0,7),(5,2,440,64,6),(10,4,369,128,6),(24,4,353,130,6),(34,1,460,16,6),(48,1,460,2,6),(66,1,396,48,6),(96,1,396,18,6),(3,128,344,36,6),(132,2,312,65,6),(132,8,99,272,6),(160,1,332,18,6),(260,8,227,16,6),(257,32,94,128,6),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(21,2,424,64,5),(27,0,484,0,5),(11,16,484,0,5),(29,0,482,0,5),(26,4,353,128,5),(50,1,460,0,5),(69,2,440,0,5),(74,4,305,128,5),(98,1,396,16,5),(133,2,312,64,5),(138,4,369,0,5),(152,4,353,2,5),(162,1,332,16,5),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(276,8,227,0,5),(273,32,78,128,5),(56,256,135,64,5),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5),(15,0,480,0,4),(39,0,344,0,4)]
def extraLevels:Nat → Packing
  | 9 => lvlNew9
  | 10 => lvlNew10
  | 11 => lvlNew11
  | 12 => lvlNew12
  | 13 => lvlNew13
  | _ => emptyPacking
def extraIndex:Nat → Nat → Option (Nat × Nat)
  | 10 => lookupNew9
  | 11 => lookupNew10
  | 12 => lookupNew11
  | 13 => lookupNew12
  | 14 => lookupNew13
  | _ => fun _ => none
def exa:Forest:=⟨511,13,dead.samples,extraCols,#[[]],extraLevels,extraIndex⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extraGeom:graphValid exa (bsB newKnown)=true:=by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk9x0:block exa 9 0 64=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk9x64:block exa 9 64 34=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allNew9:block exa 9 0 98=true:=(@z2 exa 9 0 64 34 chk9x0 chk9x64)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x0:block exa 10 0 21=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x21:block exa 10 21 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x85:block exa 10 85 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x149:block exa 10 149 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x213:block exa 10 213 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x277:block exa 10 277 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x341:block exa 10 341 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x405:block exa 10 405 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x469:block exa 10 469 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x533:block exa 10 533 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x597:block exa 10 597 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x661:block exa 10 661 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x725:block exa 10 725 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x789:block exa 10 789 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x853:block exa 10 853 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x917:block exa 10 917 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x981:block exa 10 981 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1045:block exa 10 1045 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1109:block exa 10 1109 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1173:block exa 10 1173 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1237:block exa 10 1237 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1301:block exa 10 1301 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1365:block exa 10 1365 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1429:block exa 10 1429 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1493:block exa 10 1493 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1557:block exa 10 1557 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1621:block exa 10 1621 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1685:block exa 10 1685 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1749:block exa 10 1749 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1813:block exa 10 1813 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1877:block exa 10 1877 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x1941:block exa 10 1941 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2005:block exa 10 2005 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2069:block exa 10 2069 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2133:block exa 10 2133 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2197:block exa 10 2197 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2261:block exa 10 2261 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2325:block exa 10 2325 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2389:block exa 10 2389 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2453:block exa 10 2453 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2517:block exa 10 2517 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2581:block exa 10 2581 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2645:block exa 10 2645 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2709:block exa 10 2709 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10x2773:block exa 10 2773 53=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allNew10:block exa 10 0 2826=true:=(@z2 exa 10 0 1365 1461 (@z2 exa 10 0 661 704 (@z2 exa 10 0 277 384 (@z2 exa 10 0 85 192 (@z2 exa 10 0 21 64 chk10x0 chk10x21) (@z2 exa 10 85 64 128 chk10x85 (@z2 exa 10 149 64 64 chk10x149 chk10x213))) (@z2 exa 10 277 192 192 (@z2 exa 10 277 64 128 chk10x277 (@z2 exa 10 341 64 64 chk10x341 chk10x405)) (@z2 exa 10 469 64 128 chk10x469 (@z2 exa 10 533 64 64 chk10x533 chk10x597)))) (@z2 exa 10 661 320 384 (@z2 exa 10 661 128 192 (@z2 exa 10 661 64 64 chk10x661 chk10x725) (@z2 exa 10 789 64 128 chk10x789 (@z2 exa 10 853 64 64 chk10x853 chk10x917))) (@z2 exa 10 981 192 192 (@z2 exa 10 981 64 128 chk10x981 (@z2 exa 10 1045 64 64 chk10x1045 chk10x1109)) (@z2 exa 10 1173 64 128 chk10x1173 (@z2 exa 10 1237 64 64 chk10x1237 chk10x1301))))) (@z2 exa 10 1365 704 757 (@z2 exa 10 1365 320 384 (@z2 exa 10 1365 128 192 (@z2 exa 10 1365 64 64 chk10x1365 chk10x1429) (@z2 exa 10 1493 64 128 chk10x1493 (@z2 exa 10 1557 64 64 chk10x1557 chk10x1621))) (@z2 exa 10 1685 192 192 (@z2 exa 10 1685 64 128 chk10x1685 (@z2 exa 10 1749 64 64 chk10x1749 chk10x1813)) (@z2 exa 10 1877 64 128 chk10x1877 (@z2 exa 10 1941 64 64 chk10x1941 chk10x2005)))) (@z2 exa 10 2069 384 373 (@z2 exa 10 2069 192 192 (@z2 exa 10 2069 64 128 chk10x2069 (@z2 exa 10 2133 64 64 chk10x2133 chk10x2197)) (@z2 exa 10 2261 64 128 chk10x2261 (@z2 exa 10 2325 64 64 chk10x2325 chk10x2389))) (@z2 exa 10 2453 192 181 (@z2 exa 10 2453 64 128 chk10x2453 (@z2 exa 10 2517 64 64 chk10x2517 chk10x2581)) (@z2 exa 10 2645 64 117 chk10x2645 (@z2 exa 10 2709 64 53 chk10x2709 chk10x2773))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x0:block exa 11 0 1=true:=by
  apply z0 (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1:block exa 11 1 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x65:block exa 11 65 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x129:block exa 11 129 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x193:block exa 11 193 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x257:block exa 11 257 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x321:block exa 11 321 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x385:block exa 11 385 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x449:block exa 11 449 64=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x513:block exa 11 513 16=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x529:block exa 11 529 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x593:block exa 11 593 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x657:block exa 11 657 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x721:block exa 11 721 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x785:block exa 11 785 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x849:block exa 11 849 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x913:block exa 11 913 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x977:block exa 11 977 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1041:block exa 11 1041 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1105:block exa 11 1105 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1169:block exa 11 1169 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1233:block exa 11 1233 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1297:block exa 11 1297 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1361:block exa 11 1361 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1425:block exa 11 1425 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1489:block exa 11 1489 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1553:block exa 11 1553 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1617:block exa 11 1617 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1681:block exa 11 1681 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1745:block exa 11 1745 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1809:block exa 11 1809 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1873:block exa 11 1873 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x1937:block exa 11 1937 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2001:block exa 11 2001 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2065:block exa 11 2065 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2129:block exa 11 2129 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2193:block exa 11 2193 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2257:block exa 11 2257 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2321:block exa 11 2321 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2385:block exa 11 2385 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2449:block exa 11 2449 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11x2513:block exa 11 2513 45=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allNew11:block exa 11 0 2558=true:=(@z2 exa 11 0 1233 1325 (@z2 exa 11 0 529 704 (@z2 exa 11 0 257 272 (@z2 exa 11 0 65 192 (@z2 exa 11 0 1 64 chk11x0 chk11x1) (@z2 exa 11 65 64 128 chk11x65 (@z2 exa 11 129 64 64 chk11x129 chk11x193))) (@z2 exa 11 257 128 144 (@z2 exa 11 257 64 64 chk11x257 chk11x321) (@z2 exa 11 385 64 80 chk11x385 (@z2 exa 11 449 64 16 chk11x449 chk11x513)))) (@z2 exa 11 529 320 384 (@z2 exa 11 529 128 192 (@z2 exa 11 529 64 64 chk11x529 chk11x593) (@z2 exa 11 657 64 128 chk11x657 (@z2 exa 11 721 64 64 chk11x721 chk11x785))) (@z2 exa 11 849 192 192 (@z2 exa 11 849 64 128 chk11x849 (@z2 exa 11 913 64 64 chk11x913 chk11x977)) (@z2 exa 11 1041 64 128 chk11x1041 (@z2 exa 11 1105 64 64 chk11x1105 chk11x1169))))) (@z2 exa 11 1233 640 685 (@z2 exa 11 1233 320 320 (@z2 exa 11 1233 128 192 (@z2 exa 11 1233 64 64 chk11x1233 chk11x1297) (@z2 exa 11 1361 64 128 chk11x1361 (@z2 exa 11 1425 64 64 chk11x1425 chk11x1489))) (@z2 exa 11 1553 128 192 (@z2 exa 11 1553 64 64 chk11x1553 chk11x1617) (@z2 exa 11 1681 64 128 chk11x1681 (@z2 exa 11 1745 64 64 chk11x1745 chk11x1809)))) (@z2 exa 11 1873 320 365 (@z2 exa 11 1873 128 192 (@z2 exa 11 1873 64 64 chk11x1873 chk11x1937) (@z2 exa 11 2001 64 128 chk11x2001 (@z2 exa 11 2065 64 64 chk11x2065 chk11x2129))) (@z2 exa 11 2193 192 173 (@z2 exa 11 2193 64 128 chk11x2193 (@z2 exa 11 2257 64 64 chk11x2257 chk11x2321)) (@z2 exa 11 2385 64 109 chk11x2385 (@z2 exa 11 2449 64 45 chk11x2449 chk11x2513))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12x0:block exa 12 0 56=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12x56:block exa 12 56 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12x120:block exa 12 120 64=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12x184:block exa 12 184 11=true:=by
  apply z0 (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allNew12:block exa 12 0 195=true:=(@z2 exa 12 0 120 75 (@z2 exa 12 0 56 64 chk12x0 chk12x56) (@z2 exa 12 120 64 11 chk12x120 chk12x184))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk13x0:block exa 13 0 4=true:=by
  apply z0 (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allNew13:block exa 13 0 4=true:=chk13x0
set_option maxRecDepth 16384 in
theorem extraChecks:checkedTables exa 13:=by
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
  · rfl
  · exact allNew9
  · exact allNew10
  · exact allNew11
  · exact allNew12
  · exact allNew13
def rootHard (j:Nat):=inputs.tail ++ [neg (inputs.getD 0 zero),bin true (inputs.getD 0 zero) (inputs.getD j zero)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hard1:Impossible grf 13 (rootHard 1).toFinset:=by
  have eq:targetOf exa = grf:=by decide +kernel
  rw [←eq]
  exact root_index (g:=exa) (k:=13) (top:=13) (ws:=rootHard 1) (before_sound _ newValid) extraGeom extraChecks (by decide) (i:=3) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hard2:Impossible grf 13 (rootHard 2).toFinset:=by
  have eq:targetOf exa = grf:=by decide +kernel
  rw [←eq]
  exact root_index (g:=exa) (k:=13) (top:=13) (ws:=rootHard 2) (before_sound _ newValid) extraGeom extraChecks (by decide) (i:=0) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hard3:Impossible grf 13 (rootHard 3).toFinset:=by
  have eq:targetOf exa = grf:=by decide +kernel
  rw [←eq]
  exact root_index (g:=exa) (k:=13) (top:=13) (ws:=rootHard 3) (before_sound _ newValid) extraGeom extraChecks (by decide) (i:=1) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hard6:Impossible grf 13 (rootHard 6).toFinset:=by
  have eq:targetOf exa = grf:=by decide +kernel
  rw [←eq]
  exact root_index (g:=exa) (k:=13) (top:=13) (ws:=rootHard 6) (before_sound _ newValid) extraGeom extraChecks (by decide) (i:=2) (by decide +kernel)
def srts:=inputs ++ [neg (inputs.getD 0 zero)]
def seedChoice (b:Bool) (j:Fin 10):Choice :=
  (1,srts.getD (if b then 9 else 0) zero,srts.getD j.val zero)
def rootBank (b:Bool) (j:Fin 10):=srts ++ [cvv (seedChoice b j)]
def front (b:Bool) (j:Fin 10) (u v w:Bool) :=
  (inputs.tail ++ kept u (inputs.getD 0 zero) (kept v (neg (inputs.getD 0 zero))
     (kept w (cvv (seedChoice b j)) []))).eraseDups
def frontBits (b:Bool) (j:Fin 10) (w:List Sig) :=
  let ds:=decodeBank 2 (512 + 1024*(256+(if b then 9 else 0)+16*j.val)) (wiresOf dead)
  ds.filter (fun x => w.contains x.1)
def packedWitness:List Nat:=[0x40100401008100401,0x40100401008100401,0x40100401008101201,0x40100401008140401,0x40100401008100401,0x40100401008100401,0x40120201008100401,0x40140401008100401,0x48100401008100401,0x40100401008100401,0x40100401008100401,0x40100401008100404,0x40100401008100401,0x40100401008100401,0x40100401040100401,0x40100480008100401,0x40100401008100401,0x40100401008100401,0x40100401008100401,0x40100401008100401]
def anchorPairs (b:Bool) (j:Fin 10):List (Sig × Row × Row) :=
  List.ofFn (fun i:Fin 8 =>
    let r:=((packedWitness.getD (b.toNat*10+j.val) 0) >>> (9*i.val)) &&& 511
    (inputs.getD (i.val+1) zero,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< (i.val+1)))))
set_option maxHeartbeats 0 in
theorem anchorsOk:∀ j,checkEssential grf (rootBank false j) (anchorPairs false j) = true:=by decide +kernel
theorem anchorsEq (b j):(anchorPairs b j).map Prod.fst = inputs.tail:=by
  unfold anchorPairs
  rw [List.map_ofFn]
  rfl
theorem enumerateFront {b j k t S} (hb0 : b = false) (run:Live grf k t S)
    (sub:∀ v ∈ S,v ∈ rootBank b j) :
    ∃ u v w,S=(front b j u v w).toFinset:=by
  classical
  have must (a:Sig) (ha:a ∈ inputs.tail):a ∈ S:=by
    have hh:=essential_ok (show checkEssential grf (rootBank b j) (anchorPairs b j) = true from by simpa only [hb0] using anchorsOk j) a (List.mem_toFinset.mpr ((anchorsEq b j).symm ▸ ha))
    obtain ⟨r,s,hd,iso⟩:=hh
    exact raw_required run _ _ sub _ _ hd iso
  let a:=inputs.getD 0 zero
  let n:=neg a
  let q:=cvv (seedChoice b j)
  refine ⟨decide (a∈S),decide (n∈S),decide (q∈S),?_⟩
  have eq:rootBank b j = a :: (inputs.tail ++ [n,q]):=rfl
  ext x
  simp only [List.mem_toFinset,front,List.mem_eraseDups,List.mem_append]
  change x∈S ↔ x∈inputs.tail ∨ x∈kept (decide (a∈S)) a (kept (decide (n∈S)) n (kept (decide (q∈S)) q []))
  simp only [kept]
  split_ifs <;> simp_all only [decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] <;>
    grind [List.mem_cons,List.mem_append,List.mem_singleton]
def rootRules:List (Nat × Nat):=[(0,0),(0,1),(0,2),(4,0),(10,0)]
def rootPools (b:Bool) (j:Fin 10):List BoundPool :=
  rootRules.filterMap fun (i,p) => (extraCols.read i).bind fun c =>
    materialize (vars 511)
      (kept (p.testBit 0) (2,inputs.getD 0 zero,inputs.getD 0 zero)
        (kept (p.testBit 1) (seedChoice b j) []))
      (subcube c.1 c.2.1) c.2.2.2.2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootPoolsValid (b j):∀ p ∈ rootPools b j,ValidPool (vars 511) grf p:=by
  intro p hp
  obtain ⟨⟨i,v⟩,_,hm⟩:=List.mem_filterMap.mp hp
  obtain ⟨c,hc,build⟩:=Option.bind_eq_some_iff.mp hm
  apply materialize_sound _ build
  have geo:=extraGeom
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at geo
  exact col_sound _ _ (before_sound _ newValid) (geo.1.2 c (z1.read_mem _ hc))
def rootCases (b:Bool) (j:Fin 10) (u v w:Bool) :=
  let ws:=front b j u v w
  let ds:=frontBits b j ws
  !(ws.all prB) || (sameWords (ds.map Prod.fst) ws && (coverage false ds).1 != BitVec.allOnes 768) ||
    (rootPools b j).any (fun p => poolCut p.dmn p.bound 13 p.paid p.wires ws) ||
    (!b && !u && v && w && [1,2,3,5,6,7,8].contains j.val)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem passRoots:∀ j u v w,rootCases false j u v w = true:=by decide +kernel
def rotation:=([81,130,118]:List Nat).map swapRows
theorem turned {i j:Nat} (orig:Impossible grf 13 (rootHard i).toFinset)
    (same:sameWords (rootHard j) ((rootHard i).map (movedWord rotation.reverse))=true) :
    Impossible grf 13 (rootHard j).toFinset:=by
  rw [sameWords_sound same]
  exact rotate_excluded orig rotation (by decide +kernel)
theorem frontND:∀ j u v w,(front false j u v w).Nodup:=by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem frontNo (b j u v w) (hb0 : b = false):Impossible grf 13 (front b j u v w).toFinset:=by
  let ws:=front b j u v w
  let ds:=frontBits b j ws
  have ok : rootCases b j u v w = true := by simpa only [hb0] using passRoots j u v w
  change (((!(ws.all prB) || (sameWords (ds.map Prod.fst) ws && (coverage false ds).1 != BitVec.allOnes 768)) ||
    (rootPools b j).any (fun p => poolCut p.dmn p.bound 13 p.paid p.wires ws)) ||
    (!b && !u && v && w && [1,2,3,5,6,7,8].contains j.val))=true at ok
  simp only [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true,bne_iff_ne] at ok
  intro k t hk h
  rcases ok with ((bad | ⟨eq,bad⟩) | ⟨p,hp,hcut⟩) | hh
  · have prop:ws.all prB=true:=List.all_eq_true.mpr (fun a ha => by
      have pr:=live_proper h a (List.mem_toFinset.mpr ha)
      simpa only [proper,prB,Bool.and_eq_true,bne_iff_ne] using pr)
    simp_all
  · have geo:=geomdead
    simp only [graphValid,Bool.and_eq_true,beq_iff_eq] at geo
    have pa:=chart_pairs geo.1.1.1 geo.1.1.2
    have faith:∀ a ∈ ds,faithful (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2) a:=by
      intro a ha
      exact decode_faithful _ _ _ _ _ (wires_faithful dead) a (List.mem_filter.mp ha).1
    apply bad
    rw [cov_word false ds faith]
    exact cover_sound h (sameWords_sound eq) (show Sep grf 768 _ _ _ from pair_sep pa) false (by simp)
  · obtain ⟨f,rr,bk,dom,nc,lo,hr,sup,_⟩:=rootPoolsValid b j p hp
    simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hcut
    have sh:supply bk ((ws.map z6).map (z3 f)):=by
      intro a ha
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp ha
      obtain ⟨a,hm2,rfl⟩:=List.mem_map.mp hm
      exact availableB_sound dom sup (hcut.2 a hm2)
    have lower:=projected_bound f (list_run h ws (show (front b j u v w).Nodup from by simpa only [hb0] using frontND j u v w) rfl) nc hr sh lo
    have exa:=count_constants dom ws
    have bound:=hcut.1
    omega
  · rcases hh with ⟨⟨⟨⟨hb,hu⟩,hv⟩,hw⟩,hi⟩
    subst b u v w
    fin_cases j <;> first | contradiction | exact hard1 k t hk h | exact hard2 k t hk h | exact hard3 k t hk h | exact hard6 k t hk h | exact (turned (i:=1) (j:=5) hard1 (by decide +kernel)) k t hk h | exact (turned (i:=2) (j:=8) hard2 (by decide +kernel)) k t hk h | exact (turned (i:=6) (j:=7) hard6 (by decide +kernel)) k t hk h
theorem noBank (b:Bool) (hb0 : b = false) (j:Fin 10) (C:Circuit) (hc:PEqualNP.MetaComplexity.FanInTwo C)
    (hs:C.size ≤ 13) (he:∀ r,C.eval ((rootBank b j).map (bit r)) = edge (sample r)):False:=by
  let bk:=rootBank b j
  have eq:(execute C.gates bk).getD C.output zero = grf:=by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r:Row:=⟨i,hi⟩
    change bit r _ = bit r grf
    rw [← b_read,execute_bits _ _ _ (fun g hg => (hc g hg).1)]
    exact (he r).trans (edge_table r).symm
  have mem:=get_rep (execute C.gates bk) C.output
  rw [eq] at mem
  obtain ⟨k,t,S,hk,run,sub⟩:=extract C.gates bk hc graph_proper (mem.resolve_right (fun h => h graph_proper))
  obtain ⟨u,v,w,eq⟩:=enumerateFront hb0 run sub
  exact frontNo b j u v w hb0 k t (hk.trans hs) (eq ▸ run)
theorem bankEval (b:Bool) (j:Fin 10) (r:Row) :
    (rootBank b j).map (bit r) =
    let x:=sample r
    let w:=List.ofFn x ++ [!x 0]
    w ++ [w.getD (if b then 9 else 0) false || w.getD j.val false]:=by
  have ss:srts.map (bit r) = List.ofFn (sample r) ++ [!sample r 0]:=by
    simp only [srts,List.map_append,List.map_cons,List.map_nil,bit_neg,sampled,sample]
    rfl
  change (srts ++ [bin true _ _]).map (bit r) = _
  simp only [List.map_append,List.map_cons,List.map_nil,bit_bin,ite_true]
  simp only [seedChoice,← b_read,ss]
end PEqualNP.Outside.L_meta_3178
theorem PEqualNP.Outside.L_meta_3178 : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro pins len bounds _ restricted C hc hs
  have special := restricted.2
  by_contra! he
  obtain ⟨a,b,rfl⟩ : ∃ a b : Nat, pins = [a,b] := by
    cases pins with
    | nil => simp at len
    | cons a rest =>
      cases rest with
      | nil => simp at len
      | cons b tail =>
        have h : tail=[] := List.length_eq_zero_iff.mp (by simpa using len)
        exact ⟨a,b,by simp [h]⟩
  have ha := bounds a (by simp)
  have hb := bounds b (by simp)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at special
  rcases special with rfl | rfl
  · apply PEqualNP.Outside.L_meta_3178.noBank false rfl ⟨b,hb⟩ C hc hs
    intro r
    rw [PEqualNP.Outside.L_meta_3178.bankEval]
    simpa [PEqualNP.CircuitLowerBounds.GateOp.eval,PEqualNP.Outside.L_meta_3178.edge,Bool.or_comm] using he (PEqualNP.Outside.L_meta_3178.sample r)
  · apply PEqualNP.Outside.L_meta_3178.noBank false rfl ⟨a,ha⟩ C hc hs
    intro r
    rw [PEqualNP.Outside.L_meta_3178.bankEval]
    simpa [PEqualNP.CircuitLowerBounds.GateOp.eval,PEqualNP.Outside.L_meta_3178.edge,Bool.or_comm] using he (PEqualNP.Outside.L_meta_3178.sample r)
