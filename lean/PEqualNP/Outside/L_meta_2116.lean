import Mathlib
import PEqualNP.Defs

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1674.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_2116
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def z181 (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem z51 {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem z242 {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (z181 d) b a := by
  rcases z51 h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,z181,BitVec.and_comm,BitVec.or_comm]
theorem q153 {u d} (h : allowed u d) : allowed u (z181 d) ∧ z181 (z181 d)=d := by
  rcases z51 h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [z181,allowed]
def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
private lemma z214 {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma z178 {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma z46 (i) : bit i zero = false := by simp [bit,zero]
private lemma z104 (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma z222 (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma z139 (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem z67 {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩
def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem z290 (a : Sig) : nrm false a = a := rfl
theorem j265 (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,z222]
theorem j96 {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem j94 (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,z222,neg_neg']
theorem j6 {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem j5 {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact j6 h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem z121 (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem j93 (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply z67
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,z121,ha,hb,z139,z222,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,z222,z121]
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)
private lemma q250 (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply z67 <;> intro i <;>
    simp [z139,z46,z104]
private lemma j199 : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma z229 {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b
private lemma j125 {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := q250 a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := q250 b
  by_cases he : a=b
  · subst b
    left
    rcases z51 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases z229 ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases z51 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases z51 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases z229 hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases z51 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases z51 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem z291 (a : Sig) : nrm true a ≠ one := by
  intro h
  have := j265 a
  rw [h,z104] at this
  exact Bool.noConfusion this
theorem q124 {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := j125 (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [z290] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := j93 d a b
    unfold Repr
    rw [eq]
    exact j125 e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨z291 a,z291 b⟩)
theorem z143 {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := j5 hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma z250 {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact z143 (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem j196 {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [j94]
def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma j229 (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply z67
      intro i
      cases d <;> simp [z121,z46,z104]
    cases l with
    | nil => exact Or.inl (z143 (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (z250 w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact q124 d (z250 w i) (z250 w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact z143 (Or.inr (by simp [gv,j199]))
    | cons i l => exact j196 (z250 w i)
private lemma q123 {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := z214 h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := j229 u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := q123 ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega
private lemma q251 (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (z46 _).symm
  | some a => rfl
private lemma z286 (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [q251]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact z104 _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [z121]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact z46 _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [z121]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [z222,z46]
    | cons a l => exact z222 _ _
private lemma q154 (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,z286 i g w (hg g (by simp))]
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a
def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem z145 {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem q126 {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,z145]
theorem z180 {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem q248 {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ z180 h,z180⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem q4 {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (z180 h))
  · exact Or.inl h
theorem q77 {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem q70 {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem z208 {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem j26 {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,q70 op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,q77 op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => z208 _ h,
      by simp [cost,ca,cb]⟩
theorem q44 {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases z51 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,q4 hu hb,rfl,q248 b⟩
  · exact ⟨false,inv a,b,rfl,q4 hu ha,hb,q248 a,rfl⟩
theorem q211 {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := q44 hd ha hb
  rw [e,←cx,←cy]
  exact j26 roots op hp hx hy
theorem q239 {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := q211 roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases q239 hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (q239 hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := q126 a (kept kb b rest) ka
    have hlen' := q126 b rest kb
    rw [z145] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [z145,z145]
    omega
def z12 {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem q54 {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (z12 rows) =
    kept k (z12 rows a) (ws.map (z12 rows)) := by
  cases k <;> simp [kept]
theorem z226 {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    z12 rows (comb d a b) = comb d (z12 rows a) (z12 rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem q121 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (z12 rows goal) s (ws.map (z12 rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,q54,z226] at ih ⊢
    exact Run.two op hd ka kb ih
theorem z128 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (z12 rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (z12 rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (z12 rows goal) → L ≤ q) :
    L + mass (ws.map (z12 rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (q121 rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem z120 (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem z159 (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact z120 (observe v) ⟨j,hj⟩
theorem q57 (f : Wire Row) : observe (table f) = f := by
  funext r
  exact z120 f r
theorem j91 (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact z222 _ _
theorem j92 (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,z139,comb]
  split_ifs <;> rfl
theorem q240 {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem z249 {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem z194 (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem q61 {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := z249 kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := z249 ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [z194,z194,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,q240,q240,j92] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem j81 (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←z159 (neg (table f)),j91,q57]
theorem q179 (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply z67
  intro r
  rw [z120,z121,z120,z120]
  cases d <;> rfl
theorem z168 {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply z143
    cases b
    · exact Or.inl (z67 fun i => (z120 _ i).trans (z46 i).symm)
    · exact Or.inr (z67 fun i => (z120 _ i).trans (z104 i).symm)
  · have := j81 a
    refine Or.inl ?_
    rw [←j94,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem q13 {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,q179] at sub
    have rep := q124 d (z168 ha) (z168 hb)
    obtain ⟨k',S',hk,run',sub'⟩ := q123 (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def z47 (a : Sig) : Bool := !(bit 0 a)
theorem j95 {u} {w : List Sig} (h : w.all z47=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact j96 (by simpa [z47] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem z192 {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : z47 T=true) (nR : roots.all z47=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := z168 hit
  rw [z159] at hm
  unfold Repr at hm
  rw [j96 (by simpa [z47] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := q13 h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,z159]
  rw [e,j95 nR] at hs
  exact hs
theorem z129 {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [z139,z139,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem z116 {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := z129 h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem q42 : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem z132 : proper graph := by unfold proper; decide +kernel
theorem q38 : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←q38]
  rw [List.map_ofFn]
  rfl
theorem z190 (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←q251,q154 _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem z77 (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem z86 (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := z120 _ _
theorem z89 (f : Row → Row) (a : Sig) :
    observe (rename f a) = z12 f (observe a) := by funext r; exact z86 f a r
theorem z144 (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply z67
  intro r
  simp only [z86,z139]
theorem q21 (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [z86,z86,hr] at he
  exact he
theorem z122 (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (z86 f zero ⟨j,hj⟩).trans ((z46 _).trans (z46 ⟨j,hj⟩).symm)
  · exact (z86 f one ⟨j,hj⟩).trans ((z104 _).trans (z104 ⟨j,hj⟩).symm)
theorem q199 {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := q21 f onto
  obtain ⟨fz,fo⟩ := z122 f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,z144] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem z211 {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [z139] at hp hn
      subst none
      rcases z51 hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem j197 {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem j9 {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (j197 hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem z267 {u roots T L} (hp : proper T) (nT : z47 T=true) (nR : roots.all z47=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := z192 hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact z116 run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem z138 {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply z143
    cases b
    · exact Or.inl (z67 fun i => (congrFun h i).trans (z46 i).symm)
    · exact Or.inr (z67 fun i => (congrFun h i).trans (z104 i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv
theorem q195 {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem q14 {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [z145,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem z293 {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : z47 T=true) (nR : roots.all z47=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := z192 pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact z116 run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := q61 run front nd fe
  have gc : z12 r (observe T) = observe G := (z89 _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (z12 r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←z89]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := z128 r run' (gc ▸ z138 pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (z12 r)) := by
    simp only [front,List.map_append,q195]
    let xs := (singles.toList.map observe).map (z12 r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←z89]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := q14 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def z61 (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem z240 {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem j121 {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (z61 ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (z61 ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := z214 tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,z240 (hn.erase _) b,
        z240 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [z194,z194,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := z249 kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (z61 ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,z249 ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (z61 ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := z178 tail
    have len : (z61 ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
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
theorem q213 {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem q214 {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (q213 (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := z129 h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := z211 h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem z207 {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply q214 h rfl correct
  simp
def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (z12 f (observe a))) ∧
    ¬Constant (z12 f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (z12 f (observe T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def z27 (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))
theorem q127 {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    z12 f (observe a) = z12 f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem z292 {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : z12 f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [z46] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem q24 {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : z12 f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def z107 (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (z12 f (observe a))
theorem z58 {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : z107 u f bank pool)
    (check : z27 u d pool a = true) : Available u bank (z12 f (observe a)) := by
  simp only [z27,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,z292 dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,q24 dom ho⟩)
  · exact q127 dom he ▸ supplyB v hv
  · have h := q4 hu (q127 dom he ▸ supplyB v hv)
    rw [j91] at h
    have e : inv (z12 f (inv (observe a))) = z12 f (observe a) := by
      funext r
      simp [inv,z12]
    rwa [e] at h
abbrev Choice := Nat × Sig × Sig
def z34 (c : Choice) := bin c.1 c.2.1 c.2.2
def z199 (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem q228 {u d} (h : z199 u d=true) : allowed u d := by
  simpa [z199,allowed] using h
def z165 (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  z199 u c.1 && (z27 u d pool c.2.1 && z27 u d pool c.2.2)
theorem q22 {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : z107 u f bank pool)
    (c : Choice) (valid : z165 u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ z107 u f next (z34 c :: pool) := by
  simp only [z165,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := q44 (q228 valid.1) (z58 dom hs valid.2.1)
    (z58 dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [z34,j92,z226,e]
    exact Or.inl (by simp)
  · exact z208 _ (hs _ hm)
def z160 (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if z165 u d pool c then z160 u d (z34 c::pool) cs else none
theorem z205 {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : z107 u f bank pool)
    (cs : List Choice) {result} (ok : z160 u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ z107 u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [z160] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := q22 dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def z11 (d a : Sig) := masked d a == zero || masked d a == d
theorem z184 {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (z11 d) ≤ mass ((ws.map observe).map (z12 f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,z145]
    cases h : z11 d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (z12 f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [z11,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,z292 dom hz⟩
        · exact ⟨true,q24 dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def q55 (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (z11 d)) && ws.all (z27 u d pool)
theorem z227 {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : z160 u d raw cs = some pool)
    (nd : ws.Nodup) (cut : q55 u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := z205 dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [q55,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (z12 f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact z58 dom hs (List.all_eq_true.mp all a ha)
  have b := z128 f (q61 h ws nd rfl) nc hr coveredS lo
  have massLo := z184 dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def q194 (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def z223 (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem j124 (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem j236 (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp
theorem j299 (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact j236 _ _ _
theorem j237 (r : Row) (m : Move) (a : Sig) : bit r (z223 m a) = bit (q194 m r) a := by
  simp only [z223,j299,j124,q194]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def z30 (ms : List Move) (r : Row) := ms.foldl (fun j m => q194 m j) r
def z18 (ms : List Move) (a : Sig) := ms.foldr z223 a
theorem z152 (ms : List Move) (a : Sig) (r : Row) :
    bit r (z18 ms a) = bit (z30 ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (j237 r m _).trans (ih _)
theorem z25 (ms : List Move) (a : Sig) : z18 ms a = rename (z30 ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (z152 ms a ⟨j,hj⟩).trans (z86 _ _ ⟨j,hj⟩).symm
def q71 (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem q209 {u roots w} (ok : q71 roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [q71,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext z46⟩)
  · exact Or.inr (Or.inl ⟨true,funext z104⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def z134 (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  z18 ms T == G && raw.all (fun a => q71 base (z18 ms a))
theorem z213 {u ms raw T base G} (ok : z134 ms raw T base G = true) :
    rename (z30 ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (z30 ms) a)) := by
  simp only [z134,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,z25] at ok
  exact ⟨ok.1,fun a ha => q209 (ok.2 a ha)⟩
theorem j102 {u ms raw T base G L} (ok : z134 ms raw T base G = true)
    (pT : proper T) (nT : z47 T=true) (nR : raw.all z47=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := z213 ok
  simpa using z293 pT nT nR pG (z30 ms) eq supp ∅ (by simp) (by simp) L hL
theorem q51 {u ms raw T base G L d} (ok : z134 ms raw T base G = true)
    (all : z18 ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := z213 ok
  have obs : z12 (z30 ms) (observe T) = observe G :=
    (z89 _ _).symm.trans (congrArg observe eq)
  refine ⟨z30 ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←z152,all,z104]
  · intro a ha
    rw [←z89]
    exact supp a ha
  · rw [obs]
    exact z138 properG
  · rw [obs]
    exact hL
def q45 (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem q8 {T roots a rs} (ok : q45 T roots a rs = true) : Essential T roots a := by
  simp only [q45,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def z49 (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  z47 T && raw.all z47 && xs.all (fun a => q45 T raw a.1 a.2)
theorem z118 {T raw xs} (ok : z49 T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [z49,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact q8 (List.all_eq_true.mp ok.2 _ hm)
theorem z50 {T raw xs} (ok : z49 T raw xs = true) :
    z47 T=true ∧ raw.all z47=true := by
  simp only [z49,Bool.and_eq_true] at ok
  exact ok.1
theorem q198 {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : z49 T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := z192 properT (z50 ok).1 (z50 ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := z118 ok a ha
    exact z116 run raw a sub r s hd iso
  have bound := z178 run
  omega
def q0 (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  z134 ms raw T base G && z49 T raw xs &&
    xs.all (fun a => z18 ms a.1 == zero || z18 ms a.1 == one)
theorem j280 {u ms T raw base G xs L} (ok : q0 ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [q0,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := z213 ok.1.1
  apply z293 properT (z50 ok.1.2).1 (z50 ok.1.2).2 properG _ eq supp _ (z118 ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,z25] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext z46⟩
  · rw [h]
    exact ⟨true,funext z104⟩
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def z274 (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [z274 (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def z2 (m : Nat) : Sig :=
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
def q210 (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def z64 (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def z257 (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def j13 (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def z65 (T : Sig) := T != zero && T != one
theorem z100 (T : Sig) (h : z65 T = true) : proper T := by
  simpa only [z65,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev z35 := Nat × Nat × Nat × Nat × Nat
def q224 (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def z119 (m : Nat) : Sig := z2 m
def z173 (m : Nat) (c : z35) : Nat := m % 512+512*(c.1/512)
def z198 (m : Nat) (c : z35) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := q210 z o
  let raw := z173 m c
  let free := q224 raw (z % 512) o
  let G := z18 ms (z119 m)
  let xs := z257 (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  z65 G && z134 ms (varsX raw) (z119 m) (varsX free) G &&
    (z18 ms (subcube z o)==one) &&
    (if q=0 then z49 G (varsX free) xs && decide (L ≤ count-1)
     else z65 (z2 q) &&
       q0 (q210 (q224 free q 0) 0) G (varsX free) (varsX q) (z2 q) xs &&
       decide (L ≤ prior q+count))
theorem z185 {u} {m : Nat} (c : z35) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (z2 q) (prior q))
    (ok : z198 m c prior = true) : Slice u (varsX (z173 m c)) (z119 m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := q210 z o
  let raw := z173 m (z,o,q,s,L)
  let free := q224 raw (z % 512) o
  let G := z18 ms (z119 m)
  let xs := z257 (z/512+80) s
  change (((z65 G && z134 ms (varsX raw) (z119 m) (varsX free) G) &&
    (z18 ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply q51 ok.1.1.2 ok.1.2 (z100 _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [z198,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (q198 (z100 _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [z198,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (j280 hh.1.2 (z100 _ ok.1.1.1) (z100 _ hh.1.1) (valid q) p bank hr ha)
def q225 (old rep : Nat) (swaps : List Nat) :=
  (z65 (z2 old) && z47 (z2 old) && (varsX old).all z47) && z65 (z2 rep) &&
    z134 (swaps.map z64) (varsX old) (z2 old) (varsX rep) (z2 rep)
theorem j234 {u old rep L swaps} (ok : q225 old rep swaps = true)
    (h : Lower u (varsX rep) (z2 rep) L) : Lower u (varsX old) (z2 old) L := by
  simp only [q225,Bool.and_eq_true] at ok
  exact j102 ok.2 (z100 _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (z100 _ ok.1.2) h
def z8 (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem z6 {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (z2 e.1) e.2) (q : Nat) :
    Lower u (varsX q) (z2 q) (z8 entries q) := by
  unfold z8
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2
def z79 (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (z12 f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (z12 f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ z107 u f bank c.wires ∧ True
theorem q226 {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : z160 u d raw cs = some ws) : z79 u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := z205 dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩
theorem q46 {u raw T c} (valid : z79 u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, z27 u c.domain c.wires a = true)
    (buy : if paid then z165 u c.domain c.wires choice = true
       else z27 u c.domain c.wires (z34 choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(z34 choice :: rest).countP (z11 c.domain))
    (nd : (z34 choice :: rest).Nodup) :
    Impossible u T k (z34 choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := z34 choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : z107 u f out (z34 choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (z12 f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := z128 f (q61 run ws nd rfl) nc reach covered lo
    have cm := z184 dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (z11 c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact z58 dom hs buy
    · exact z58 dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := q22 dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (z12 f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact z58 dom point (known _ hm)
def z59 (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := z34 op
  let extra := !(z27 u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (z11 c.domain)) &&
    rest.all (z27 u c.domain c.wires)) && (!extra || z165 u c.domain c.wires op)
theorem z127 {u raw T c} (valid : z79 u raw T c) {k rest op}
    (nd : (z34 op::rest).Nodup) (cut : z59 u c k rest op = true) :
    Impossible u T k (z34 op::rest).toFinset := by
  let extra := !(z27 u c.domain c.wires (z34 op))
  apply q46 valid k rest op extra _ _ _ nd
  · simp only [z59,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [z59,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : z27 u c.domain c.wires (z34 op) <;> simp_all [extra]
  · simp only [z59,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (z160 u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem z246 {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : z79 u raw T c := by
  unfold materialize at h
  cases he : z160 u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact q226 slice cs he
abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def z176 {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem z83 {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (z176 r v).getLsbD i.val = bit (r i) v := by
  simp only [z176,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def z101 (r s : Fin 768 → Row) (a : Sig) : Signals := (z176 r a,z176 s a)
def z74 (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem q237 {T r s} (h : z74 T r s) : Sep T 768 r s (z101 r s) := by
  exact ⟨h,fun a i => ⟨z83 _ _ _,z83 _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = z101 r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem j7 {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    z176 r (bin d a b) = bv d (z176 r a) (z176 r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := z83 r (bin d a b) ⟨j,hj⟩
  rw [z139,←z83 r a ⟨j,hj⟩,←z83 r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem z182 {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,z101,j7,hx,hy]
def z33 : Decor := (zero,0,0)
theorem z268 (r s) : faithful r s z33 := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (z176 r zero).getLsbD j
    rw [show (z176 r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from z83 _ _ ⟨j,hj⟩,z46]
    simp
  · change (0 : Bits).getLsbD j = (z176 s zero).getLsbD j
    rw [show (z176 s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from z83 _ _ ⟨j,hj⟩,z46]
    simp
theorem z263 {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i z33) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact z268 _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def z148 (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) z33
    let b := ws.getD ((bits >>> 4) &&& 15) z33
    z148 k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem z183 (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ z148 n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact z182 _ (z263 base _) (z263 base _)
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem q223 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem q222 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem q221 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem q220 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem q219 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem q218 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem q217 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem q216 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem q215 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem z56 : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact q223 r
  · exact q222 r
  · exact q221 r
  · exact q220 r
  · exact q219 r
  · exact q218 r
  · exact q217 r
  · exact q216 r
  · exact q215 r
theorem q6 (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [z56]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def z276 (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem z201 {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem q122 (m) (p q : Nat → Bits) :
    ∀ a ∈ z276 m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := z201 hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (q6 p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (z83 _ _ ⟨i,hi⟩).symm
  · exact (q6 q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (z83 _ _ ⟨i,hi⟩).symm
def q62 (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem j29 (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using q6 v i j
  · simp [vertex,hh,z46]
theorem q160 (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (z2 m) = (q62 m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := j29 m v i ⟨j,hj⟩
  simp only [bit,z2,q62,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits
def z155 (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => z155 (column d a.2) c) (0,0,0)
def z158 (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def z245 (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem j298 (c : Cov) (a : Bits) : z158 (z155 a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [z158,z155,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem j297 (c : Cov) (a b : Bits) : z245 (z155 a (z155 b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [z245,z155,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem j248 (c : Cov) (a b : Bits) : z155 a (z155 b c)=z155 b (z155 a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [z155,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [z155,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem q247 (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (z155 (column d a.2)) ih
  | swap a b t => exact j248 _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem q246 (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (z101 r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (z101 r s a.1) ||| _
    rw [show a.2=z101 r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def z171 (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def z69 (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  z171 (z171 ws a ka) b kb
theorem z219 {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem q158 {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (z171 ws a keep)).1 =
      (if keep then (coverage d ws).1 else z158 (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = z158 (coverage d ws) _
    rw [q247 d (z219 a ha)]
    exact (j298 _ _).symm
  · rfl
theorem q212 {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (z219 a ha).trans (List.Perm.cons _ (z219 b hm))
theorem q157 {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (z69 ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else z158 (coverage d ws) (column d b.2))
       else if kb then z158 (coverage d ws) (column d a.2)
       else z245 (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = z245 (coverage d ws) _ _
    rw [q247 d (q212 a b ha hb ne)]
    exact (j297 _ _ _).symm
  · exact q158 d a ha false
  · exact q158 d b hb false
  · rfl
def z142 (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem z99 {xs ys} (h : z142 xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [z142,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def z130 (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def q145 (xs : List Sig) := xs.foldl (fun v x => v+z130 x) 0
def z85 (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := z34 op::rest
  (links (q145 ws)).any (z142 ws) || pools.any (fun p => z59 u p k rest op)
theorem z270 {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, z79 u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (z34 op :: rest).Nodup)
    (h : z85 u pools links k rest op = true) :
    Impossible u T k (z34 op :: rest).toFinset := by
  simp only [z85,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [z99 ok]
    exact lValid _ _ hx
  · exact z127 (pValid _ hp) nd ok
abbrev j154 := Cov × Bool
def z204 (u : Bool) (ws : List Decor) : j154 := (coverage (!u) ws,u)
def z137 (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else z158 v b) else if kb then z158 v a else z245 v a b
theorem z252 (ws : List Decor) (a : Decor) (k : Bool) : (z171 ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem q242 (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (z69 ws a b ka kb).Sublist ws := (z252 _ _ _).trans (z252 _ _ _)
theorem q241 (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (z69 ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [z69,z171,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def z44 (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
abbrev z17 := Nat × Nat × List Decor × j154 × List BoundPool × (Nat → List (List Sig))
def z103 (c : z17) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := z137 cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !z65 z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (z69 ws a b ka kb).map Prod.fst
      z85 cov.2 pools links (cap-1) rest (z44 op a b)
def z233 (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (z69 ws a b ka kb).map Prod.fst
theorem q17 {u raw T r s ws pools links cap a b op ka kb}
    (pairs : z74 T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, z79 u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : z103 (cap,ws.length,ws,z204 u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (z233 ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := z69 ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := q242 _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : z65 z.1 = true := by simpa [z65,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,q241 _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := z178 h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold z103 at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := z207 h (q237 pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (z101 r s) (rest.map Prod.fst) :=
    q246 _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = z137 (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    q157 d a b ha hb ne ka kb
  have hf := z182 op (faith _ ha) (faith _ hb)
  change column d (z101 r s z.1) ||| covered d (z101 r s) (rest.map Prod.fst) = _ at sep
  change z.2 = z101 r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((z137 (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (z137 (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !z65 z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact z270 (op:=z44 op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def z156 (ctx : z17) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := z103 ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem z228 {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases z51 h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def q177 (ctx : z17) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (z156 ctx a b))
def z157 (ctx : z17) : List Decor → Bool
  | [] => true
  | a::bs => q177 ctx a bs && z157 ctx bs
theorem j47 {ctx ws} (h : z157 ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → z156 ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → z156 ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [z157,Bool.and_eq_true,q177,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (z228 hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (z228 hd)
      · exact ih h.2 haTail hbTail
theorem q178 {ctx a b d} (h : z156 ctx a b d = true) (ka kb : Bool) :
    z103 ctx d a b (dbin d a b) ka kb = true := by
  simp only [z156,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem q243 {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem q23 {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ z171 v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [z171,nd.mem_erase_iff,and_comm]
theorem z256 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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
theorem q37 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (z69 ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (z252 ws a ka)
  simp only [z69,List.mem_map,q23 wn,q23 dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (z256 nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (z256 nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem z264 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (z233 ws d a b ka kb).toFinset =
      (z61 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [z233,z61,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    q37 nd ha hb,q243,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem z241 {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (z61 v a b d ka kb).toFinset = (z61 v b a (z181 d) kb ka).toFinset := by
  ext x
  simp only [z61,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    q243,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,z242 hd a b]
  tauto
theorem j8 {u raw T r s ws pools links cap}
    (pairs : z74 T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, z79 u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : z157 (cap,ws.length,ws,z204 u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply j121 nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : z156 (cap,ws.length,ws,z204 u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (z61 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←z264 nd aa bb ne']
    exact q17 pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (q178 test ka kb)
  rcases j47 checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [z241 _ nd _ _ d hd]
    exact one b a (z181 d) hbW haW (Ne.symm ne) kb ka (z242 hd a.1 b.1 ▸ pro)
      (z242 hd a.1 b.1 ▸ fresh) (hh _ (q153 hd).1)
theorem q167 (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← q38]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (z56 i r).symm.trans ((h _ hm).trans (z56 i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def z253 (p q : List Move) := inputs.all (fun a => z18 p (z18 q a) == a)
theorem z164 {p q} (h : z253 p q = true) (r : Row) :
    z30 q (z30 p r) = r := by
  apply q167
  intro a ha
  rw [←z152,←z152]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def q5 (T : Sig) (p : List Move) :=
  (z18 p T == T) && z253 p p.reverse && z253 p.reverse p
theorem z289 {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : q5 T p = true) : Impossible u T n (ws.map (z18 p.reverse)).toFinset := by
  simp only [q5,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (z30 p) := fun r => ⟨z30 p.reverse r,z164 ok.2 r⟩
  intro k hk h
  have run := q199 h (z30 p) onto
  have goal : rename (z30 p) T = T := (z25 p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (z30 p) (z18 p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [z86,z152,z164 ok.1.2]
  have back : (ws.map (z18 p.reverse)).toFinset.image (rename (z30 p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def z38 : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def z60 (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def z15 (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := z60 data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := z60 data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List z35 × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List z35 := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2
def z136 (g : Forest) :=
  let ws := z276 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem z200 (g : Forest) : ∀ a ∈ z136 g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact q122 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def z29 (g : Forest) := z119 g.mask
def z78 (m : Nat) (v : Nat → Bits) :=
  q62 m v
theorem j123 (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (z119 m) = (z78 m v).getLsbD i.val := by
  exact q160 m v i
theorem z166 {m : Nat} {p q : Nat → Bits}
    (hp : z78 m p = BitVec.allOnes 768) (hq : z78 m q = 0) :
    z74 (z119 m) (asRow p) (asRow q) := by
  intro i
  simp only [j123,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def z71 {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::z71 (bits >>> 1) ws else z71 (bits >>> 1) ws
theorem z202 {α : Type} (bits : Nat) (ws : List α) : (z71 bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold z71
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def z106 (_g : Forest) (depth : Nat) := depth
def z191 (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := z136 g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*z106 g depth
  let width := len+raw.length+depth
  let recp := z60 data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := z148 depth ops raw
  (ops,bank,z71 (recp >>> len) bank)
def q149 (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def z299 (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := z299 bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (q149 ops 8 2,(bank.getD (ops &&& 15) z33).1,
        (bank.getD (q149 ops 4 4) z33).1) :: more
def z151 (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (z173 g.mask ci)) (z299 bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem z186 (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (z173 g.mask ci)) (z29 g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : z151 g ops depth bank i paid = some c) :
    z79 g.mode (vars g.mask) (z29 g) c := by
  unfold z151 at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply z246 _ h
    exact cols ci (List.mem_of_getElem? e)
def z236 (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := z60 data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: z236 data w v n (pos+w+v)
def z52 (g : Forest) (k i : Nat) := (z191 g k i).2.2.map Prod.fst
def z90 (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (z52 g k pair.1).map (z18 (perm.map z64).reverse)
theorem z294 (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, q5 (z29 g) (x.map z64) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (z29 g) k (z52 g k i).toFinset)
    {pair out} (h : z90 g k pair = some out) :
    Impossible g.mode (z29 g) k out.toFinset := by
  unfold z90 at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact z289 (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def z96 (g : Forest) (k i : Nat) :=
  let raw := z136 g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := z191 g k i
  let values := ws.map Prod.fst
  let start := num*(10*z106 g depth+raw.length+depth)
  let pos := start+num*offw+z60 data (start+i*offw) offw
  let nr := z60 data pos 5
  let nl := z60 data (pos+5) lw
  let st := pos+5+lw
  let rules := (z236 data cw depth nr st).filterMap (fun (a,b) => z151 g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (z90 g (k-1))).toList
  decide values.Nodup && !(values.contains (z29 g)) &&
    (if k=0 then true else z157 (k,ws.length,ws,z204 g.mode ws,rules,ls) ws)
theorem z131 (g : Forest) (k i : Nat)
    (samples : z74 (z29 g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (z173 g.mask ci)) (z29 g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, q5 (z29 g) (x.map z64) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (z29 g) (k-1) (z52 g (k-1) j).toFinset)
    (checked : z96 g k i = true) : Impossible g.mode (z29 g) k (z52 g k i).toFinset := by
  simp only [z96,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : z29 g ∉ z52 g k i := by simpa [z52] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (z52 g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply j8 (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply z183 _ _ _ _ _ (z200 g) v
    exact (z202 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact z186 g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (z90 g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact z294 g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => z96 g k (start+n) && block g k start n
theorem q249 {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    z96 g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem z10 {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def z28 (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def z24 (g : Forest) (prior : Nat → Nat) :=
  (z78 g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (z78 g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => z198 g.mask c prior) &&
  g.autos.all (fun p => q5 (z29 g) (p.map z64))
theorem j23 (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (z2 q) (prior q))
    (geometry : z24 g prior = true) (rows : z28 g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (z29 g) k (z52 g k i).toFinset := by
  simp only [z24,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply z131 g 0 i (z166 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => z185 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact q249 (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply z131 g _ i (z166 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => z185 _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact q249 (rows _ hk) i (by omega) (by omega)
def z110 (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && z142 (z52 g k i) ws
theorem j4 {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (z2 q) (prior q))
    (geom : z24 g prior = true) (blocks : z28 g top) (le : k ≤ top)
    (idx : z110 g k i ws = true) : Impossible g.mode (z29 g) k ws.toFinset := by
  simp only [z110,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←z99 idx.2]
  exact j23 g top prior low geom blocks _ le i idx.1
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (z2 e.1) e.2
def z9 (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem z5 {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (z2 m) L)
    (ok : carries.all (fun v => q225 v.1 m v.2) = true) :
    Known u (z9 old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact j234 (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem q165 : Known true [] := by simp [Known]
theorem j11 {u es} (h : Known true es) : Known u es := fun e he => j9 (h e he)
def z55 (v : Nat) (upper : Nat) := 2^769*upper+v
def z21 {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => z55 (f x).toNat (z21 f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => z55 1 (units n)
theorem z295 (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem j90 (a b : Bits) (u v : Nat) :
    z55 a.toNat u &&& z55 b.toNat v = z55 (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [z55,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (z295 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem j198 (a b : Bits) (u v : Nat) :
    z55 a.toNat u ||| z55 b.toNat v = z55 (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [z55,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (z295 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem j89 (a b : Bits) (u v : Nat) :
    z55 a.toNat u ^^^ z55 b.toNat v = z55 (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [z55,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (z295 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem z179 {α} (f g : α → Bits) (xs) :
    z21 f xs &&& z21 g xs = z21 (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [z21]
  | cons a xs ih => simp only [z21,j90,ih]
theorem z277 {α} (f g : α → Bits) (xs) :
    z21 f xs ||| z21 g xs = z21 (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [z21]
  | cons a xs ih => simp only [z21,j198,ih]
theorem z235 {α} (f g : α → Bits) (xs) :
    z21 f xs ^^^ z21 g xs = z21 (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [z21]
  | cons a xs ih => simp only [z21,j89,ih]
def z146 (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem j193 (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,z55,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem j221 (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
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
theorem j100 {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (z146 (units xs.length) (z21 f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [z146,Nat.testBit_and,Nat.testBit_shiftRight,j193 _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [z21,List.length_cons,units,z55]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using j221 (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev z188 := Nat × Nat
abbrev q7 := Nat × Nat × Nat
def z75 {α} (s : α → Signals) (xs : List α) : z188 :=
  (z21 (fun x => (s x).1) xs,z21 (fun x => (s x).2) xs)
def z175 {α} (c : α → Cov) (xs : List α) : q7 :=
  (z21 (fun x => (c x).1) xs,z21 (fun x => (c x).2.1) xs,
   z21 (fun x => (c x).2.2) xs)
def z37 (d : Bool) (a : z188) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem z273 (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem z82 {α} (s : α → Signals) (xs : List α) (d : Bool) :
    z37 d (z75 s xs) = z21 (fun x => column d (s x)) xs := by
  cases d <;> simp only [z37,z75,column,Bool.false_eq_true,ite_false,ite_true,z179,z235,z273]
def z123 (op : Nat) (a b : z188) : z188 :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem q125 {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    z123 op (z75 (fun x => (a x).2) xs) (z75 (fun x => (b x).2) xs) =
    z75 (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [z123,h0,ite_true,z75,z179,dbin,bv]
  by_cases h1 : op=1
  · simp [z123,h1,z75,z277,dbin,bv]
  by_cases h2 : op=2
  · simp [z123,h2,z75,z179,z235,z273,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [z123,h0,h1,h2,ite_false,z75,z179,z235,z273,dbin,bv,e]
def z125 (c : q7) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem z224 {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    z125 (z175 c xs) (z21 a xs) (z21 b xs) ka kb =
    z21 (fun x => z137 (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [z125,z175,z179,z277,z235,z273,z137,z158,z245,
      Bool.false_eq_true,ite_false,ite_true]
def z3 (c : z17) (i : Nat) := c.2.2.1.getD i z33
def z221 (c : z17) (i j op : Nat) (ka kb : Bool) :=
  let a := z3 c i
  let b := z3 c j
  z103 c op a b (dbin op a b) ka kb
def z150 (c : z17) (d ka kb : Bool) (op i j : Nat) :=
  let a := z3 c i
  let b := z3 c j
  z137 c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def z210 {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && z210 f (mask >>> 769) xs
theorem q128 {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : z210 f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [z210,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
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
abbrev Batch := Nat × Nat × Nat × List z188 × q7
def z48 (k n : Nat) (xs : List z17) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => z75 (fun c => (z3 c i).2) xs),
    z175 (fun c => c.2.2.2.1.1) xs)
def z112 (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem z161 (k n) (xs) {i : Nat} (h : i<n) :
    z112 (z48 k n xs) i = z75 (fun c => (z3 c i).2) xs := by
  simp [z112,z48,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem q196 (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply z67
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def z36 (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem q130 (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (z171 ws a keep).countP p + z36 p a keep := by
  cases keep
  · simp only [z171,Bool.false_eq_true,ite_false,z36,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [z171,z36]
theorem j104 (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - z36 p a ka - z36 p b kb ≤
    (z69 ws a b ka kb).countP p := by
  have h1 := q130 p ws a ka
  have h2 := q130 p (z171 ws a ka) b kb
  simp only [z69]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem z114 {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def z162 {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem z216 {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : z162 f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => z162 f l fun xs => k (x::xs)) = _
    rw [z114,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem z230 (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem z153 (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem z231 (d a : Sig) : nconst d.toNat (nmask d.toNat a) = z11 d a := by
  rw [z230]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←z153,z0]
  rw [nconst,e,z153]
  rfl
theorem q252 (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,z230,z153,List.map_cons,List.any_cons,Bool.beq_comm]
theorem z232 (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = z27 u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [q196]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,z231,z230,x,q252,q252]
  simp only [z27,z11]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (z27 u p.domain p.wires w.1) 0 1
def z275 (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => z11 p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - z36 const a ka - z36 const b kb + (z11 p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!z27 u p.domain p.wires z).toNat < p.bound+cm)) &&
    (z27 u p.domain p.wires z || (z27 u p.domain p.wires a.1 && z27 u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [z230]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply z67
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply z67
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply z67
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply z67
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem q238 (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = z36 (fun w : Decor => z11 d w.1) a keep := by
  rw [nloss,z231,z36]
  cases keep
  · cases z11 d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def z174 (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def q152 {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def z238 {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => z162 (nmask d) p.wires fun pm => z162 (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => q152 u fun u => f (d,c,l,t,v,ms,pm,u)
theorem q151 {β : Type} (u k ws p) (f : QS → β) : z238 u k ws p f = f (z174 u k ws p) := by
  have e (b : Bool) (f : Bool → β) : q152 b f = f b := by cases b <;> rfl
  simp only [z238,z114,z216,e]
  rfl
noncomputable def z196 {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => z238 u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem q73 {β : Type} (u k ws ps) (f : List QS → β) : z196 u k ws ps f = f (ps.map (z174 u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change z238 u k ws p (fun q => z196 u k ws ps fun qs => f (q::qs)) = _
    rw [q151,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := z17 × Nat × Nat × List QS × List Nat × Nat
noncomputable def z102 (c : z17) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (z174 c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def z197 {β : Type} (cs : List z17) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    z162 (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    z196 c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem z124 {β : Type} (cs) (f : List Lane → β) : z197 cs f = f (cs.map z102) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      z162 (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      z196 c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => z197 cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [z114,z114,z216,z114,q73,ih]
    rfl
noncomputable def q75 (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem j194 {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i z33).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem j119 {u k p ws i j op ka kb} (h : q75 (z174 u k ws p) i j op ka kb=true) :
    z275 u p ws k (ws.getD i z33) (ws.getD j z33) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [z232]
    rfl
  simp only [q75,z174,z114,j194 _ _ z0,su,List.countP_map,Function.comp_def,z231] at h
  generalize ws.getD i z33=a at h ⊢
  generalize ws.getD j z33=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => z11 p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => z11 p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => z11 p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,z231,z232,z232,z232,q238,q238] at h
  have ca : z11 p.domain (bin op a.1 b.1)=true → z27 u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [z27,z11,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [z275,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => z11 p.domain w.1) - z36 (fun w : Decor => z11 p.domain w.1) a ka -
      z36 (fun w : Decor => z11 p.domain w.1) b kb = c at h ⊢
    generalize z11 p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize z27 u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]
theorem q166 (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def j103 (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => z162 (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem j12 (xs : List Sig) : q145 xs = (xs.map z130).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+z130 x) a = a+(xs.map z130).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem q43 (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((z69 ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [z69,z171,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem q74 {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : z199 u op=true)
    (h : z275 u p ws k a b op ka kb=true) :
    z59 u p k ((z69 ws a b ka kb).map Prod.fst) (z44 op a b)=true := by
  let const := fun w : Decor => z11 p.domain w.1
  let z := bin op a.1 b.1
  let rest := z69 ws a b ka kb
  have ck := j104 const ws a b ka kb
  change ws.countP const - z36 const a ka - z36 const b kb ≤ rest.countP const at ck
  simp only [z275,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := q43 (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((z69 ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (z27 u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : z27 u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!z27 u p.domain p.wires z) || z165 u p.domain p.wires (z44 op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [z165,z44,x,y,al]
  change k+p.paid+(!z27 u p.domain p.wires z).toNat < p.bound+(ws.countP const - z36 const a ka -
        z36 const b kb+(z11 p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : z34 (z44 op a b)=z := rfl
  simp only [z59,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!z27 u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if z11 p.domain z then 1 else 0)
  cases hc' : z11 p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem j48 (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [z230]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i z33).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem j59 {c : z17} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (z3 c i).1 ≠ (z3 c j).1 := by
  have gi : z3 c i = c.2.2.1[i] := by simp [z3,List.getD_eq_getElem?_getD,hi]
  have gj : z3 c j = c.2.2.1[j] := by simp [z3,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem j10 {c : z17} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : j103 fl (z102 c) i j op ka kb=true) :
    (c.2.2.2.2.2 (q145 (z34 (z44 op (z3 c i) (z3 c j)) ::
      (z69 c.2.2.1 (z3 c i) (z3 c j) ka kb).map Prod.fst))).any (z142
      (z34 (z44 op (z3 c i) (z3 c j)) ::
      (z69 c.2.2.1 (z3 c i) (z3 c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : z3 c t ∈ c.2.2.1 := by
    simp [z3,List.getD_eq_getElem?_getD,ht]
  have hne := j59 nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : z3 c i ≠ z3 c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := q37 nd ha hb ka kb v
  have sum := q43 (fun w : Decor => z130 w.1) ha hb hab ka kb
  have wi : z3 c i = c.2.2.1.getD i z33 := rfl
  have wj : z3 c j = c.2.2.1.getD j z33 := rfl
  simp only [j103,z102,z114,getW,←wi,←wj,j48] at h
  generalize z3 c i=a at *
  generalize z3 c j=b at *
  change Option.rec false _ (fl (z130 (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (z130 a.1)) - (cond kb 0 (z130 b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => z130 w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : q145 (z34 (z44 op a b) :: (z69 c.2.2.1 a b ka kb).map Prod.fst) =
      z130 (bin op a.1 b.1)+((z69 c.2.2.1 a b ka kb).map (fun w : Decor => z130 w.1)).sum := by
    rw [j12,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize q145 (z34 (z44 op a b) :: (z69 c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [z216,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,q166,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [z142,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def z147 (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => q75 s i j op ka kb) (j103 fl l i j op ka kb))) (z221 l.1 i j op ka kb)
theorem z206 {c : z17} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : z147 fl (z102 c) i j op ka kb=true) :
    z221 c i j op ka kb=true := by
  simp only [z147,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : z199 c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [z199] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : z3 c t ∈ c.2.2.1 := by
      simp [z3,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := j59 nd hi hj (fun e => by simp [e] at hn)
    have closed := q74 (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (j119 ok)
    have cut : c.2.2.2.2.1.any (fun p => z59 c.2.2.2.1.2 p (c.1-1)
        ((z69 c.2.2.1 (z3 c i) (z3 c j) ka kb).map Prod.fst)
        (z44 op (z3 c i) (z3 c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [z221,z103,z85,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := j10 nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [z221,z103,z85,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def z285 (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def z115 (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem q295 : ∀ v : Fin 144, z115 v.val=true → ∀ t : Fin 9, z285 v.val t.val<9 ∧
    z223 (z64 v.val) (inputs.getD t.val zero) = inputs.getD (z285 v.val t.val) zero := by decide +kernel
theorem q296 {v t : Nat} (hv : z115 v=true) (ht : t<9) : z285 v t<9 ∧
    z223 (z64 v) (inputs.getD t zero) = inputs.getD (z285 v t) zero := by
  have lt : v<144 := by
    simp only [z115,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact q295 ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => z285 v t) t
theorem j220 {perm : List Nat} (ok : perm.all z115=true) {t : Nat} (ht : t<9) :
    z18 (perm.map z64).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [z18,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := q296 ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def q76 : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => q76 n (bits >>> 10) (ws++[z])
theorem j27 (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (z148 n bits ds).map (fun w => F w.1) = q76 n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i z33).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [q76,z114,z148,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem q11 {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (z71 bits ws).map f = z71 bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,z71,z71]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def z298 (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (z60 data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  z71 (rec >>> len) (q76 depth (rec &&& ((1 <<< len)-1)) raw)
theorem z262 (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all z115=true) :
    z298 g k i perm = ((z52 g k i).map (z18 (perm.map z64).reverse)).map BitVec.toNat := by
  let ms := (perm.map z64).reverse
  let F (a : Sig) : Nat := (z18 ms a).toNat
  have F0 : F zero=0 := by
    change (z18 ms zero).toNat=0
    rw [z25,(z122 _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (z18 ms (bin op a b)).toNat = zN op (z18 ms a).toNat (z18 ms b).toNat
    rw [j48,z25,z144,z25,z25]
  have raw : (z136 g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [z136,z276,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := z201 hm
    exact congrArg BitVec.toNat (j220 ok hj)
  have len : (z136 g).length = (selected g.mask).length := by simp [z136,z276]
  unfold z298 z52 z191
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [z114,z106,len]
  rw [List.map_map,List.map_map,q11,←raw,←j27 F F0 Fb]
  rfl
noncomputable def z247 (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all z115) (some (z298 g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (z247 g (k-1))
noncomputable def q164 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := z112 b i
    let b' := z112 b j
    let z := z123 op a b'
    let mask := z146 r (z125 cov (z37 (!u) a) (z37 (!u) b') ka kb ||| z37 (!u) z)
    z210 (fun c => z147 fl c i j op ka kb) mask xs
theorem q163 {fl u} (k n) (xs : List z17) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : q164 fl u (z48 k n xs) (xs.map z102) i j op ka kb=true) :
    z221 xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : z221 xs[q] i j op ka kb =
      if len>k then true else if z150 xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
      else if !z65 (dbin op (z3 xs[q] i) (z3 xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (z3 xs[q] i) (z3 xs[q] j)).1)
      then true else z85 u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((z69 xs[q].2.2.1 (z3 xs[q] i) (z3 xs[q] j) ka kb).map Prod.fst)
        (z44 op (z3 xs[q] i) (z3 xs[q] j)) := by
    simp only [z221,z103,budget,arity,mode,len,z150] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := z112 (z48 k n xs) i
    let b := z112 (z48 k n xs) j
    let cov := z175 (fun c : z17 => c.2.2.2.1.1) xs
    change (if len>k then true else z210 _ (z146 r
       (z125 cov (z37 (!u) a) (z37 (!u) b) ka kb |||
        z37 (!u) (z123 op a b))) (xs.map z102)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := z161 k n xs hi
    have cb : b = _ := z161 k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,q125,z82,z82,z82,z224,z277] at pass
    by_cases hit : z150 xs[q] (!u) ka kb op i j = BitVec.allOnes 768
    · apply z206 nd hfl
      have m := q128 _ _ _ q (by simpa using hq) (by
        rw [j100 _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def q162 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := q164 fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def z284 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (q162 fl u b xs i j))
noncomputable def z154 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => z284 fl u b xs i js && z154 fl u b xs js
theorem q161 {fl u} (k n) (xs : List z17) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : z154 fl u (z48 k n xs) (xs.map z102) js=true) :
    z157 xs[q] (js.map (z3 xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [z154,Bool.and_eq_true,z284,List.all_eq_true] at allRows
    simp only [List.map_cons,z157,q177,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @q163 fl u k n xs i j op
    simp only [q162,Bool.and_eq_true] at pass
    simp only [z156,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def q52 (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List z17) :=
    z154 fl u (z48 k n xs) (xs.map z102) (List.range n)
theorem q193 {fl u k n} {xs : List z17} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : q52 fl u k n xs=true) : z157 xs[q] xs[q].2.2.1=true := by
  have all := q161 k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (z3 xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [z3,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def z149 (g : Forest) (k i : Nat) : z17 :=
  let raw := z136 g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := z191 g k i
  let start := num*(10*z106 g depth+raw.length+depth)
  let pos := start+num*offw+z60 data (start+i*offw) offw
  let nr := z60 data pos 5
  let nl := z60 data (pos+5) lw
  let st := pos+5+lw
  let rules := (z236 data cw depth nr st).filterMap (fun (a,b) => z151 g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (z90 g (k-1))).toList
  (k,ws.length,ws,z204 g.mode ws,rules,ls)
theorem j295 (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (z149 g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (z90 g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,z247] at h
    simp only [Option.bind_some,z90]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all z115 with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(z52 g (k-1) pair.1).map (z18 (perm.map z64).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (z262 g _ _ hv)
def prelim (T : Sig) (c : z17) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem q150 (g : Forest) (k i : Nat) :
    z96 g k i = (prelim (z29 g) (z149 g k i) &&
      (if k=0 then true else z157 (z149 g k i) (z149 g k i).2.2.1)) := rfl
theorem j101 {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → z96 g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (z149 g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (z29 g) c)
noncomputable def z203 (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := z48 k ar xs
  z197 xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    z284 (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem z287 {g k start n ar lo len} (h : z203 g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    z284 (flOf g k) g.mode (z48 k ar (contexts g k start n)) ((contexts g k start n).map z102)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [z203,z124] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem q120 {g k start n ar lo a b}
    (h : z203 g k start n ar lo a=true) (t : z203 g k start n ar (lo+a) b=true) :
    z203 g k start n ar lo (a+b)=true := by
  simp only [z203,z124]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact z287 h (lo+j) (by omega) (by omega)
  · exact z287 t (lo+j) (by omega) (by omega)
theorem j296 {g k start n ar} (h : z203 g k start n ar 0 ar=true) :
    q52 (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      z154 (flOf g k) g.mode (z48 k ar xs) (xs.map z102) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,z154,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := z287 h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold q52
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem j122 {g k start n ar} (hd : header g k start n ar=true)
    (h : z203 g k start n ar 0 ar=true) : block g k start n=true := by
  apply j101
  intro i lo hi
  let xs := contexts g k start n
  have hm : z149 g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => j295 g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [q150,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ q193 hq hb ha hm nd hfl hn (j296 h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => z203 g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem j235 {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    z203 g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := q120 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem z1 {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact j122 h.1 (j235 h.2)
  | succ d ih =>
    have v := z10 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def z40 {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => z40 f (xs.take (xs.length/2)) d ∧ z40 f (xs.drop (xs.length/2)) d
theorem z14 {α f xs d} (h : @z40 α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem q297 {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => z104 r,fun a ha => ?_,z138 pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)
theorem z258 {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (z2 q) (prior q))
    (e : (z2 q == z2 m && (varsX q == vars m) && (prior q == cap+1) && z65 (z2 m) &&
      decide (vars m).Nodup && q55 u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (z2 m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact z227 (q297 (z100 _ e4) h) [] rfl e5 e6
theorem z53 {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (z2 q) (prior q)) (ci : z35)
    (ok : z198 m ci prior = true)
    (cut : (decide ws.Nodup && q55 u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (z173 m ci)) ws)=true) :
    Impossible u (z2 m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact z227 (z185 ci prior low ok) [] rfl cut.1 cut.2
theorem z26 {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (z2 q) (prior q))
    (geom : z24 g prior = true) (blocks : z28 g cap)
    (idx : z110 g cap i ws = true) : Impossible u (z2 m) cap ws.toFinset := by
  subst hm
  subst hu
  exact j4 low geom blocks (Nat.le_refl _) idx
def essOK (m hints : Nat) : Bool :=
  let xs := j13 m hints
  z65 (z2 m) && z49 (z2 m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem z68 {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (z2 m) cap (vars m).toFinset) : Lower u (vars m) (z2 m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply z267 (z100 _ ok.1.1) (z50 ok.1.2).1 (z50 ok.1.2).2 _ a
  intro v hv
  apply z118 ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def j192 (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def q245 (m : Nat) (rs : List Nat) : Bool :=
  let xs := j192 m rs
  z49 (z2 m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    z65 (z2 m) && decide (varsX m = vars m ++ [z274 (m/512-1)])
theorem j22 {u} {m : Nat} {rs : List Nat} (ok : q245 m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (z2 m) k S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [q245,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := z118 ess v (List.mem_toFinset.mpr hv)
    exact z116 h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=z274 (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : z274 (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem z16 {u} {m q cap : Nat} {rs : List Nat} (ok : q245 m rs = true)
    (e : z2 m = z2 q) (ev : vars m = vars q)
    (a : Impossible u (z2 q) cap (vars q).toFinset)
    (b : Impossible u (z2 q) cap (varsX m).toFinset) :
    Lower u (varsX m) (z2 m) (cap+1) := by
  have ok' := ok
  simp only [q245,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := z192 (z100 _ ok'.1.2) (z50 ok'.1.1.1).1 (z50 ok'.1.1.1).2 hr ha
  by_contra! small
  rcases j22 ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def j19 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47473,0x173652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe97a7f,0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def j20 : List z35 := []
def j233 : List (List Nat) := [[],[48,33]]
def j116 : Nat → Packing
  | 3 => g15l3
  | _ => z38
def j232 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => j19[j]?.getD (0,0),j20,j233,j116,j232⟩
set_option maxHeartbeats 0 in
theorem j282 : z24 g15 (z8 []) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=0) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j195 : block g15 3 0 1=true := by
  apply z1 (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem j247 : block g15 3 0 1=true := j195
theorem j80 : z28 g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact j247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (z2 15) 4 := z68 (hints:=8449) (by decide +kernel) (z26 (g:=g15) (i:=0) rfl rfl (z6 [] q165) j282 j80 (by decide +kernel))
def unitMask : Sig := 0x10000000000000000000000000000000100000000000000010000000100010116
def maskForbid4 : Sig := 0x2000000000000000000000000000000220000000000000302000000000000070200000100000003220000050000000722
def maskForbid6 : Sig := 0x50007000000000000000000000000001500370000000000000000000000000004040400000000000000000004040400040404
def maskForbid7 : Sig := 0x1000300000000000000000000000000000000000110111001000300015051500100030
def z39 (v : Nat) : Sig :=
  if v == 4 then maskForbid4 else if v == 6 then maskForbid6 else if v == 7 then maskForbid7 else zero
def in4 : Sig := inputs.getD 4 zero
def in6 : Sig := inputs.getD 6 zero
def in7 : Sig := inputs.getD 7 zero
def is467 (a : Sig) : Bool := (a == in4) || (a == in6) || (a == in7)
def z54 (a : Sig) : Sig :=
  if a == in4 then maskForbid4 else if a == in6 then maskForbid6 else if a == in7 then maskForbid7 else zero
def z109 (a : Sig) : Bool := inputs.contains a
def z88 (v other : Sig) (op : Nat) (kv : Bool) : Bool :=
  if is467 v then (op == 1) && (!kv) && (!z109 other) && ((other &&& unitMask) == zero) && ((other &&& z54 v) == zero)
  else true
def z31 (a b : Sig) (op : Nat) (ka kb : Bool) : Bool :=
  z88 a b op ka && z88 b a op kb
theorem z255 (a b : Sig) (op : Nat) (ka kb : Bool) :
    z31 a b op ka kb = z31 b a op kb ka := by
  simp only [z31, Bool.and_comm]
def in4N : Nat := in4.toNat
def in6N : Nat := in6.toNat
def in7N : Nat := in7.toNat
def q80 : Nat := unitMask.toNat
def z261 : Nat := maskForbid4.toNat
def z260 : Nat := maskForbid6.toNat
def z259 : Nat := maskForbid7.toNat
def q200 : List Nat := inputs.map BitVec.toNat
def j106 (a : Nat) : Bool := Nat.beq a in4N || Nat.beq a in6N || Nat.beq a in7N
def q60 (a : Nat) : Nat :=
  if Nat.beq a in4N then z261 else if Nat.beq a in6N then z260 else if Nat.beq a in7N then z259 else 0
noncomputable def z193 (v other op : Nat) (kv : Bool) : Bool :=
  if j106 v then
    Nat.beq op 1 && (!kv) && (!anyEq other q200) &&
      Nat.beq (Nat.land other q80) 0 && Nat.beq (Nat.land other (q60 v)) 0
  else true
noncomputable def z169 (a b op : Nat) (ka kb : Bool) : Bool :=
  z193 a b op ka && z193 b a op kb
theorem j105 (a : Sig) : j106 a.toNat = is467 a := by
  simp only [j106, is467, in4N, in6N, in7N, z153]
theorem q197 (a : Sig) : q60 a.toNat = (z54 a).toNat := by
  have z0 : (0 : Nat) = zero.toNat := by simp [zero]
  simp only [q60, z54, in4N, in6N, in7N, z261, z260, z259, z153]
  cases (a == in4) <;> cases (a == in6) <;> cases (a == in7) <;> simp [z0]
theorem q78 (x : Sig) : anyEq x.toNat q200 = z109 x := by
  rw [Bool.eq_iff_iff, q166, q200, List.mem_map]
  simp only [z109, List.contains_eq_mem, decide_eq_true_eq]
  exact ⟨fun ⟨y, hy, he⟩ => BitVec.toNat_inj.mp he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
theorem q56 (a b : Sig) (op : Nat) (k : Bool) :
    z193 a.toNat b.toNat op k = z88 a b op k := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have z0 : (0 : Nat) = zero.toNat := by simp [zero]
  have h1 : Nat.beq op 1 = (op == 1) := by rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
  simp only [z193, z88, j105, q78, q197, q80, tn, z0, z153, h1]
theorem z272 (a b : Sig) (op : Nat) (ka kb : Bool) :
    z169 a.toNat b.toNat op ka kb = z31 a b op ka kb := by
  simp only [z169, z31, q56]
theorem inputs_nodup : inputs.Nodup := by decide +kernel
theorem q41 : in4 ≠ in6 := by decide +kernel
theorem q40 : in4 ≠ in7 := by decide +kernel
theorem q39 : in6 ≠ in7 := by decide +kernel
theorem j99 : z54 in4 = z39 4 := by decide +kernel
theorem j98 : z54 in6 = z39 6 := by decide +kernel
theorem j97 : z54 in7 = z39 7 := by decide +kernel
theorem q59 : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
    z54 (inputs.getD v.val zero) = z39 v.val := by decide +kernel
theorem z296 : ∀ u : Fin 9, bit (Fin.ofNat 512 (1 <<< u.val)) (inputs.getD u.val zero) = true := by decide +kernel
theorem q159 : ∀ u : Fin 9, bit (Fin.ofNat 512 (1 <<< u.val)) unitMask = true := by decide +kernel
theorem z271 : ∀ r : Row, bit r unitMask = (List.finRange 9).any (fun j => decide (r.val = 1 <<< j.val)) := by decide +kernel
theorem q18 : ∀ (r : Row) (v : Fin 9), r.val ^^^ (1 <<< v.val) < 512 := by decide +kernel
theorem q10 : ∀ (r : Row) (t v : Fin 9), t ≠ v →
    (r.val ^^^ (1 <<< v.val)).testBit t.val = r.val.testBit t.val := by
  intro r t v hne
  have hlt : t.val ≠ v.val := Fin.val_ne_of_ne hne
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  simp [hlt, Eq.comm]
theorem z135 : ∀ v : Fin 9, ∃ r : Row, bit r graph ≠ bit r (inputs.getD v.val zero) := by decide +kernel
theorem z254 : ∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∀ r : Row,
    bit r (z39 v.val) = true →
    sample r v = false ∧ bit r graph = false ∧
      bit (Fin.ofNat 512 (r.val ^^^ (1 <<< v.val))) graph = true := by decide +kernel
set_option maxRecDepth 8192 in
theorem z218 : ∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∀ u : Fin 9, u ≠ v →
    ∃ r : Row, bit r (z39 v.val) = true ∧ (r.val &&& (1 <<< u.val)) = (1 <<< u.val) := by decide +kernel
def ok467 (U : Finset Sig) (a b : Sig) (d : Nat) : Prop :=
  z31 a b d (decide (a ∈ U)) (decide (b ∈ U)) = true
def Live467 (target : Sig) : Nat → Finset Sig → Prop
  | 0, S => S = {target} ∧ proper target
  | k + 1, S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed false d ∧
      ok467 U a b d ∧ S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live467 target k (insert (bin d a b) U)
theorem Live467.stop {target : Sig} (hp : proper target) : Live467 target 0 {target} := ⟨rfl, hp⟩
theorem Live467.binary {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (hd : allowed false d) (hok : ok467 U a b d) (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live467 target k (insert (bin d a b) U)) :
    Live467 target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, hok, rfl, ha, hb, hab, hfresh, tail⟩
theorem Live467.ind {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live467 target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live467.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed false d)
      (hok : ok467 U a b d) (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live467 target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (Live467.binary hd hok ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live467 target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, hok, rfl, ha, hb, hab, hf, tail⟩ := h
    exact binary hd hok ha hb hab hf tail (ih tail)
theorem z63 {target k S} (h : Live467 target k S) : Live false target k S := by
  induction h using Live467.ind with
  | stop hp => exact Live.stop hp
  | binary hd _ ha hb hab hf _ ih => exact Live.binary hd ha hb hab hf ih
def z23 (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live467 T k S
theorem q69 {T cap S} (h : Impossible false T cap S) : z23 T cap S :=
  fun k hk hl => h k hk (z63 hl)
def z187 (T : Sig) (p : List Move) : Bool :=
  q5 T p &&
  inputs.all (fun a => inputs.contains (z18 p a)) &&
  (z18 p unitMask == unitMask) &&
  ([4, 6, 7] : List Nat).all fun v =>
    let y := z18 p (inputs.getD v zero)
    is467 y && (z18 p (z39 v) == z54 y)
theorem q16 {T k S} (h : Live467 T k S) (f : Row → Row) (onto : Function.Surjective f)
    (hin : ∀ a ∈ inputs, rename f a ∈ inputs)
    (hu : rename f unitMask = unitMask)
    (h4 : is467 (rename f in4) = true ∧ rename f maskForbid4 = z54 (rename f in4))
    (h6 : is467 (rename f in6) = true ∧ rename f maskForbid6 = z54 (rename f in6))
    (h7 : is467 (rename f in7) = true ∧ rename f maskForbid7 = z54 (rename f in7)) :
    Live467 (rename f T) k (S.image (rename f)) := by
  have inj := q21 f onto
  obtain ⟨fz, fo⟩ := z122 f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)), fun e => p.2 (inj (e.trans fo.symm))⟩
  have hraw : ∀ x, z109 (rename f x) = z109 x := by
    have hsub : (inputs.map (rename f)).toFinset ⊆ inputs.toFinset := by
      intro y hy
      rw [List.mem_toFinset, List.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      exact List.mem_toFinset.mpr (hin a ha)
    have hnd : (inputs.map (rename f)).Nodup := inputs_nodup.map inj
    have heq : (inputs.map (rename f)).toFinset = inputs.toFinset := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup inputs_nodup, List.length_map]
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [z109, List.contains_eq_mem, decide_eq_true_eq]
    constructor
    · intro hx
      have hm : rename f x ∈ (inputs.map (rename f)).toFinset := by rw [heq]; exact List.mem_toFinset.mpr hx
      rw [List.mem_toFinset, List.mem_map] at hm
      obtain ⟨a, ha, e⟩ := hm
      exact inj e ▸ ha
    · intro hx
      exact hin x hx
  let g3 : Fin 3 → Sig := fun
    | 0 => in4
    | 1 => in6
    | _ => in7
  have hg3_inj : Function.Injective g3 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [g3] at hij
    · rfl
    · exact False.elim (q41 hij)
    · exact False.elim (q40 hij)
    · exact False.elim (q41 hij.symm)
    · rfl
    · exact False.elim (q39 hij)
    · exact False.elim (q40 hij.symm)
    · exact False.elim (q39 hij.symm)
    · rfl
  have hm_iff (y : Sig) : is467 y = true ↔ ∃ k : Fin 3, g3 k = y := by
    simp only [is467, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((rfl | rfl) | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨k, rfl⟩
      fin_cases k <;> simp [g3]
  have hex_phi (k : Fin 3) : ∃ j : Fin 3, g3 j = rename f (g3 k) := by
    apply (hm_iff _).mp
    fin_cases k
    · exact h4.1
    · exact h6.1
    · exact h7.1
  choose φ hφ using hex_phi
  have hφ_inj : Function.Injective φ := fun i j e =>
    hg3_inj (inj (by rw [← hφ i, ← hφ j, e]))
  have hφ_surj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ_inj
  have his467 : ∀ x, is467 (rename f x) = is467 x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [hm_iff, hm_iff]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨k, rfl⟩ := hφ_surj j
      exact ⟨k, inj ((hφ k).symm.trans hj)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨φ k, hφ k⟩
  have hmask : ∀ x, is467 x = true → rename f (z54 x) = z54 (rename f x) := by
    intro x hx
    simp only [is467, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with (rfl | rfl) | rfl
    · rw [j99, show z39 4 = maskForbid4 by rfl, h4.2]
    · rw [j98, show z39 6 = maskForbid6 by rfl, h6.2]
    · rw [j97, show z39 7 = maskForbid7 by rfl, h7.2]
  have hside (a b : Sig) (op : Nat) (k : Bool) : z88 (rename f a) (rename f b) op k = z88 a b op k := by
    simp only [z88, his467]
    by_cases ha : is467 a = true
    · simp only [ha, if_true, hraw]
      have eu : ((rename f b &&& unitMask) == zero) = ((b &&& unitMask) == zero) := by
        conv_lhs => rw [← hu, show rename f b &&& rename f unitMask = rename f (b &&& unitMask) from (z144 f 0 b unitMask).symm, ← fz]
        simp [beq_iff_eq, inj.eq_iff]
      have em : ((rename f b &&& z54 (rename f a)) == zero) = ((b &&& z54 a) == zero) := by
        conv_lhs => rw [← hmask a ha, show rename f b &&& rename f (z54 a) = rename f (b &&& z54 a) from (z144 f 0 b (z54 a)).symm, ← fz]
        simp [beq_iff_eq, inj.eq_iff]
      rw [eu, em]
    · simp [ha]
  induction h using Live467.ind with
  | stop hp => simpa using Live467.stop (pp _ hp)
  | @binary k U a b d hd hok ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    have hok' : ok467 (U.image (rename f)) (rename f a) (rename f b) d := by
      simp only [ok467, z31, Finset.mem_image, inj.eq_iff, exists_eq_right, hside] at hok ⊢
      exact hok
    simp only [Finset.image_insert, z144] at fresh ih ⊢
    exact Live467.binary hd hok' (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem z225 {T n} {ws : List Sig} (hi : z23 T n ws.toFinset)
    (p : List Move) (ok : z187 T p = true) : z23 T n (ws.map (z18 p.reverse)).toFinset := by
  simp only [z187, q5, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ok
  obtain ⟨⟨⟨⟨⟨ht, hc1⟩, hc2⟩, hin⟩, hu⟩, h4, h6, h7⟩ := ok
  have onto : Function.Surjective (z30 p) := fun r => ⟨z30 p.reverse r, z164 hc2 r⟩
  have hin' : ∀ a ∈ inputs, rename (z30 p) a ∈ inputs := fun a ha => by
    have h := hin a ha
    simp only [List.contains_eq_mem, decide_eq_true_eq] at h
    exact (z25 p a) ▸ h
  have hu' : rename (z30 p) unitMask = unitMask := (z25 p unitMask).symm.trans hu
  have hf4 : is467 (rename (z30 p) in4) = true ∧ rename (z30 p) maskForbid4 = z54 (rename (z30 p) in4) := by
    have h4' : is467 (z18 p in4) = true ∧ z18 p maskForbid4 = z54 (z18 p in4) := h4
    rw [z25, z25] at h4'
    exact h4'
  have hf6 : is467 (rename (z30 p) in6) = true ∧ rename (z30 p) maskForbid6 = z54 (rename (z30 p) in6) := by
    have h6' : is467 (z18 p in6) = true ∧ z18 p maskForbid6 = z54 (z18 p in6) := h6
    rw [z25, z25] at h6'
    exact h6'
  have hf7 : is467 (rename (z30 p) in7) = true ∧ rename (z30 p) maskForbid7 = z54 (rename (z30 p) in7) := by
    have h7' : is467 (z18 p in7) = true ∧ z18 p maskForbid7 = z54 (z18 p in7) := h7
    rw [z25, z25] at h7'
    exact h7'
  intro k hk h
  have run := q16 h (z30 p) onto hin' hu' hf4 hf6 hf7
  have goal : rename (z30 p) T = T := (z25 p T).symm.trans ht
  have inv (x : Sig) : rename (z30 p) (z18 p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j, hj⟩ _ = bit ⟨j, hj⟩ _
    rw [z86, z152, z164 hc1]
  have back : (ws.map (z18 p.reverse)).toFinset.image (rename (z30 p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_, ⟨a, ha, rfl⟩, inv a⟩
  rw [goal, back] at run
  exact hi k hk run
theorem q155 {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed false d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (z61 ws a b d ka kb).length ≤ cap →
      z31 a b d ka kb = true →
      z23 T (cap - 1) (z61 ws a b d ka kb).toFinset) :
    z23 T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live467.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd hok ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := z214 (z63 tail) _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b by rfl, z240 (hn.erase _) b, z240 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [z194, z194, er, he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := z249 kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (z61 ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, z249 ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (z61 ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := z178 (z63 tail)
    have len : (z61 ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd, eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len hok k (by omega) (eq.symm ▸ tail)
theorem z220 {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, z79 false raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → z23 T k (List.toFinset xs))
    (nd : (z34 op :: rest).Nodup)
    (h : z85 false pools links k rest op = true) :
    z23 T k (z34 op :: rest).toFinset := by
  simp only [z85, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨xs, hx, ok⟩ | ⟨p, hp, ok⟩
  · rw [z99 ok]
    exact lValid _ _ hx
  · exact q69 (z127 (pValid _ hp) nd ok)
def z66 (c : z17) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  if !z31 a.1 b.1 op ka kb then true else z103 c op a b z ka kb
theorem z251 {raw T r s ws pools links cap a b op ka kb}
    (pairs : z74 T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools, z79 false raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → z23 T (cap - 1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (hok : z31 a.1 b.1 op ka kb = true)
    (test : z66 (cap, ws.length, ws, z204 false ws, pools, links) op a b (dbin op a b) ka kb = true) :
    z23 T (cap - 1) (z233 ws op a b ka kb).toFinset := by
  rw [z66, if_neg (by simp [hok])] at test
  let z := dbin op a b
  let rest := z69 ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := q242 _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : z65 z.1 = true := by simpa [z65, proper] using pro
  have leq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, q241 _ _ _ _ _ ha hb ne, Nat.add_comm 1]
  intro k hk h
  have hsz := z178 (z63 h)
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold z103 at test
  change (if 1 + (ws.length - _ - _) > cap then true else _) = true at test
  rw [leq, if_neg (by omega)] at test
  have sep := z207 (z63 h) (q237 pairs)
  let d := !false
  have g : (coverage d rest).1 = covered d (z101 r s) (rest.map Prod.fst) :=
    q246 _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = z137 (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    q157 d a b ha hb ne ka kb
  have hf := z182 op (faith _ ha) (faith _ hb)
  change column d (z101 r s z.1) ||| covered d (z101 r s) (rest.map Prod.fst) = _ at sep
  change z.2 = z101 r s z.1 at hf
  rw [← hf, ← g, rz, BitVec.or_comm] at sep
  dsimp only [d] at sep
  have be : ((z137 (coverage (!false) ws) (column (!false) a.2) (column (!false) b.2) ka kb ||| column (!false) z.2) != BitVec.allOnes 768) = false := by
    simp only [sep, bne_self_eq_false]
  change (if (z137 (coverage (!false) ws) (column (!false) a.2) (column (!false) b.2) ka kb ||| column (!false) z.2) != BitVec.allOnes 768 then true else if !z65 z.1 || ws.any (fun v => v.1 == z.1) then true else _) = true at test
  rw [be, pp, fr] at test
  exact z220 (op := z44 op a b) (rest := rest.map Prod.fst) pv lv ndc test k hk h
def z92 (ctx : z17) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := z66 ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def z244 (ctx : z17) (a : Decor) (bs : List Decor) :=
  bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (z92 ctx a b))
def z81 (ctx : z17) : List Decor → Bool
  | [] => true
  | a :: bs => z244 ctx a bs && z81 ctx bs
theorem q79 {ctx ws} (h : z81 ctx ws = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) : (∀ d, allowed ctx.2.2.2.1.2 d → z92 ctx a b d = true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → z92 ctx b a d = true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [z81, Bool.and_eq_true, z244, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (z228 hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (z228 hd)
      · exact ih h.2 haTail hbTail
theorem q9 {ctx a b d} (h : z92 ctx a b d = true) (ka kb : Bool) :
    z66 ctx d a b (dbin d a b) ka kb = true := by
  simp only [z92, Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem q58 {raw T r s ws pools links cap}
    (pairs : z74 T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, z79 false raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → z23 T (cap - 1) (List.toFinset xs))
    (checks : z81 (cap, ws.length, ws, z204 false ws, pools, links) ws = true) :
    z23 T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap = 0
  · intro k hk h
    have ke : k = 0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he, hS]; exact Finset.mem_singleton_self _))
  have hc' : 0 < cap := by omega
  apply q155 nd out
  intro a ha b hb d hd ka kb ne fresh pro len hok
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (hok' : z31 a.1 b.1 d ka kb = true)
      (test : z92 (cap, ws.length, ws, z204 false ws, pools, links) a b d = true) :
      z23 T (cap - 1) (z61 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [← z264 nd aa bb ne']
    exact z251 pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr hok' (q9 test ka kb)
  rcases q79 checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh hok (hh d hd)
  · have hfd : z181 d = d := by
      rcases z51 hd with rfl | rfl | ⟨hf, _⟩ | ⟨hf, _⟩
      · rfl
      · rfl
      · exact Bool.noConfusion hf
      · exact Bool.noConfusion hf
    have hok' : z31 b.1 a.1 (z181 d) kb ka = true := by
      rw [hfd, z255]
      exact hok
    rw [z241 _ nd _ _ d hd]
    exact one b a (z181 d) hbW haW (Ne.symm ne) kb ka (z242 hd a.1 b.1 ▸ pro)
      (z242 hd a.1 b.1 ▸ fresh) hok' (hh _ (q153 hd).1)
def z76 (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  z90 g k pair
theorem z234 (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, z187 (z29 g) (x.map z64) = true)
    (earlier : ∀ i < (g.levels k).1, z23 (z29 g) k (z52 g k i).toFinset)
    {pair out} (h : z76 g k pair = some out) :
    z23 (z29 g) k out.toFinset := by
  unfold z76 z90 at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e, Option.map_some, Option.some.injEq] at h
      subst out
      exact z225 (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def z62 (g : Forest) (k i : Nat) :=
  let raw := z136 g
  let (num, depth, cw, iw, pw, offw, lw, data) := g.levels k
  let (ops, bank, ws) := z191 g k i
  let values := ws.map Prod.fst
  let start := num * (10 * z106 g depth + raw.length + depth)
  let pos := start + num * offw + z60 data (start + i * offw) offw
  let nr := z60 data pos 5
  let nl := z60 data (pos + 5) lw
  let st := pos + 5 + lw
  let rules := (z236 data cw depth nr st).filterMap (fun (a, b) => z151 g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (z76 g (k - 1))).toList
  decide values.Nodup && !(values.contains (z29 g)) &&
    (if k = 0 then true else z81 (k, ws.length, ws, z204 false ws, rules, ls) ws)
theorem z117 (g : Forest) (k i : Nat) (hf : g.mode = false)
    (samples : z74 (z29 g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice false (varsX (z173 g.mask ci)) (z29 g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, z187 (z29 g) (x.map z64) = true)
    (prior : k > 0 → ∀ j < (g.levels (k - 1)).1, z23 (z29 g) (k - 1) (z52 g (k - 1) j).toFinset)
    (checked : z62 g k i = true) : z23 (z29 g) k (z52 g k i).toFinset := by
  simp only [z62, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : z29 g ∉ z52 g k i := by simpa [z52] using checked.1.2
  by_cases h0 : k = 0
  · subst k
    intro t lo h
    have ht : t = 0 := by omega
    subst t
    generalize he : (z52 g 0 i).toFinset = S at h
    obtain ⟨hS, _⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he, hS]; exact Finset.mem_singleton_self _))
  apply q58 (raw := vars g.mask) samples _ hN hT _ _ (by simpa only [h0, if_false] using checked.2)
  · intro v hv
    apply z183 _ _ _ _ _ (z200 g) v
    exact (z202 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a, b⟩, _, h⟩ := List.mem_filterMap.mp hp
    simpa [hf] using z186 g (by simpa [hf] using cols) h
  · intro tag xs hx
    have e : ((g.index k tag).bind (z76 g (k - 1))) = some xs := by simpa using hx
    obtain ⟨pair, _, h⟩ := Option.bind_eq_some_iff.mp e
    exact z234 g _ names (prior (by omega)) h
def z13 (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => z62 g k (start + n) && z13 g k start n
theorem q1 {g k start n} (h : z13 g k start n = true) (j : Nat) (lo : start ≤ j) (hi : j < start + n) :
    z62 g k j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [z13, Bool.and_eq_true] at h
    by_cases eq : j = start + n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem z7 {g k start a b} (h : z13 g k start a = true)
    (h' : z13 g k (start + a) b = true) : z13 g k start (a + b) = true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [z13, Bool.and_eq_true] at h'
    simp only [Nat.add_succ, z13, Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1, ih h'.2⟩
def z91 (g : Forest) (top : Nat) :=
  ∀ k ≤ top, z13 g k 0 (g.levels k).1 = true
def z84 (g : Forest) (prior : Nat → Nat) :=
  (z78 g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (z78 g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => z198 g.mask c prior) &&
  g.autos.all (fun p => z187 (z29 g) (p.map z64))
noncomputable def z111 (c : z17) (i j op : Nat) (ka kb : Bool) :=
  z66 c op (z3 c i) (z3 c j) (dbin op (z3 c i) (z3 c j)) ka kb
noncomputable def z163 (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y =>
  or (not (z169 x y op ka kb)) (z147 fl l i j op ka kb)
theorem z217 {c : z17} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys = xs.map BitVec.toNat)
    (h : z163 fl (z102 c) i j op ka kb = true) :
    z111 c i j op ka kb = true := by
  simp only [z163, z114, z102, getW, z272, Bool.or_eq_true] at h
  change (!z31 (z3 c i).1 (z3 c j).1 op ka kb) = true ∨ z147 fl (z102 c) i j op ka kb = true at h
  rcases h with hno | hfb
  · simp [z111, z66, hno]
  · by_cases hallow : z31 (z3 c i).1 (z3 c j).1 op ka kb = true
    · have hf := z206 nd hfl hfb
      simp only [z111, z66, hallow, Bool.not_true, Bool.false_eq_true, if_false]
      exact hf
    · simp [z111, z66, hallow]
noncomputable def z266 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k, n, r, _, cov) := b
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > k then true else
    let a := z112 b i
    let b' := z112 b j
    let z := z123 op a b'
    let mask := z146 r (z125 cov (z37 (!u) a) (z37 (!u) b') ka kb ||| z37 (!u) z)
    z210 (fun c => z163 fl c i j op ka kb) mask xs
theorem q3 {fl u} (k n) (xs : List z17) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (arity : xs[q].2.1 = n) (mode : xs[q].2.2.2.1.2 = u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys = zs.map BitVec.toNat)
    (pass : z266 fl u (z48 k n xs) (xs.map z102) i j op ka kb = true) :
    z111 xs[q] i j op ka kb = true := by
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  have eval : z111 xs[q] i j op ka kb =
      if !z31 (z3 xs[q] i).1 (z3 xs[q] j).1 op ka kb then true
      else if len > k then true else if z150 xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
      else if !z65 (dbin op (z3 xs[q] i) (z3 xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1 == (dbin op (z3 xs[q] i) (z3 xs[q] j)).1)
      then true else z85 xs[q].2.2.2.1.2 xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k - 1)
        ((z69 xs[q].2.2.1 (z3 xs[q] i) (z3 xs[q] j) ka kb).map Prod.fst)
        (z44 op (z3 xs[q] i) (z3 xs[q] j)) := by
    simp only [z111, z66, z103, budget, arity, mode, len, z150] <;> rfl
  by_cases small : len > k
  · rw [eval]
    split <;> simp [small]
  · let r := units xs.length
    let a := z112 (z48 k n xs) i
    let b := z112 (z48 k n xs) j
    let cov := z175 (fun c : z17 => c.2.2.2.1.1) xs
    change (if len > k then true else z210 _ (z146 r
       (z125 cov (z37 (!u) a) (z37 (!u) b) ka kb |||
        z37 (!u) (z123 op a b))) (xs.map z102)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := z161 k n xs hi
    have cb : b = _ := z161 k n xs hj
    dsimp only [r, cov] at pass
    rw [ca, cb, q125, z82, z82, z82, z224, z277] at pass
    by_cases hit : z150 xs[q] (!u) ka kb op i j = BitVec.allOnes 768
    · apply z217 nd hfl
      have m := q128 _ _ _ q (by simpa using hq) (by
        rw [j100 _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval]
      by_cases hallow : z31 (z3 xs[q] i).1 (z3 xs[q] j).1 op ka kb = true
      · rw [if_neg (by simp [hallow]), if_neg small, if_pos (bne_iff_ne.mpr hit)]
      · simp [hallow]
noncomputable def z265 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := z266 fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def z167 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
  js.all (fun j => (opsOf u).all (z265 fl u b xs i j))
noncomputable def z98 (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i :: js => z167 fl u b xs i js && z98 fl u b xs js
theorem q2 {fl u} (k n) (xs : List z17) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (arity : xs[q].2.1 = n) (mode : xs[q].2.2.2.1.2 = u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys = zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j < n) (allRows : z98 fl u (z48 k n xs) (xs.map z102) js = true) :
    z81 xs[q] (js.map (z3 xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [z98, Bool.and_eq_true, z167, List.all_eq_true] at allRows
    simp only [List.map_cons, z81, z244, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_, ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j, hj, rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @q3 fl u k n xs i j op
    simp only [z265, Bool.and_eq_true] at pass
    simp only [z92, Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1, check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩, check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def z209 (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List z17) :=
  z98 fl u (z48 k n xs) (xs.map z102) (List.range n)
theorem q12 {fl u k n} {xs : List z17} {q} (hq : q < xs.length)
    (hb : xs[q].1 = k) (ha : xs[q].2.1 = n) (hm : xs[q].2.2.2.1.2 = u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys = zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length = n)
    (pass : z209 fl u k n xs = true) : z81 xs[q] xs[q].2.2.1 = true := by
  have all := q2 k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (z3 xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [z3, List.getD_eq_getElem?_getD, h2]
  rwa [eq] at all
def z97 (g : Forest) (k i : Nat) : z17 :=
  let raw := z136 g
  let (num, depth, cw, iw, pw, offw, lw, data) := g.levels k
  let (ops, bank, ws) := z191 g k i
  let start := num * (10 * z106 g depth + raw.length + depth)
  let pos := start + num * offw + z60 data (start + i * offw) offw
  let nr := z60 data pos 5
  let nl := z60 data (pos + 5) lw
  let st := pos + 5 + lw
  let rules := (z236 data cw depth nr st).filterMap (fun (a, b) => z151 g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (z76 g (k - 1))).toList
  (k, ws.length, ws, z204 false ws, rules, ls)
theorem j24 (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag = some ys) :
    ∃ xs ∈ (z97 g k i).2.2.2.2.2 tag, ys = xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (z76 g (k - 1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp, Option.bind_some, z247] at h
    simp only [Option.bind_some, z76, z90]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha, Option.bind_some] at h
        cases hv : perm.all z115 with
        | false => simp [hv] at h
        | true =>
          simp only [hv, cond_true, Option.some.injEq] at h
          refine ⟨(z52 g (k - 1) pair.1).map (z18 (perm.map z64).reverse), ?_, ?_⟩
          · simp [v]
          · exact h.symm.trans (z262 g _ _ hv)
theorem z297 (g : Forest) (k i : Nat) :
    z62 g k i = (prelim (z29 g) (z97 g k i) &&
      (if k = 0 then true else z81 (z97 g k i) (z97 g k i).2.2.1)) := rfl
theorem q129 {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → z62 g k i = true) :
    z13 g k start n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [z13, Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega), ih (fun i le lt => h i le (by omega))⟩
def z93 (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start + ·)).map (z97 g k)
def q148 (g : Forest) (k start n ar : Nat) :=
  (z93 g k start n).all (fun c => c.2.1 == ar && prelim (z29 g) c)
noncomputable def z87 (g : Forest) (k start n ar lo len : Nat) :=
  let xs := z93 g k start n
  let b := z48 k ar xs
  z197 xs fun ys => (List.range len).all (fun d =>
    let i := lo + d
    z167 (flOf g k) false b ys i (List.range' (i + 1) (ar - (i + 1))))
theorem z172 {g k start n ar lo len} (h : z87 g k start n ar lo len = true)
    (i : Nat) (l : lo ≤ i) (r : i < lo + len) :
    z167 (flOf g k) false (z48 k ar (z93 g k start n)) ((z93 g k start n).map z102)
      i (List.range' (i + 1) (ar - (i + 1))) = true := by
  simp only [z87, z124] at h
  have ha := List.all_eq_true.mp h (i - lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem z288 {g k start n ar lo a b}
    (h : z87 g k start n ar lo a = true) (t : z87 g k start n ar (lo + a) b = true) :
    z87 g k start n ar lo (a + b) = true := by
  simp only [z87, z124]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j < a
  · exact z172 h (lo + j) (by omega) (by omega)
  · exact z172 t (lo + j) (by omega) (by omega)
theorem j28 {g k start n ar} (h : z87 g k start n ar 0 ar = true) :
    z209 (flOf g k) false k ar (z93 g k start n) = true := by
  let xs := z93 g k start n
  have go (lo num : Nat) (eq : lo + num = ar) :
      z98 (flOf g k) false (z48 k ar xs) (xs.map z102) (List.range' lo num) = true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ, z98, Bool.and_eq_true]
      refine ⟨?_, ih (lo + 1) (by omega)⟩
      have ok := z172 h lo (by omega) (by omega)
      simpa only [show ar - (lo + 1) = num by omega] using ok
  unfold z209
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem q156 {g k start n ar} (hd : q148 g k start n ar = true)
    (h : z87 g k start n ar 0 ar = true) : z13 g k start n = true := by
  apply q129
  intro i lo hi
  let xs := z93 g k start n
  have hm : z97 g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_map.mpr ⟨i - start, List.mem_range.mpr (by omega), by omega⟩, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true, beq_iff_eq] at one
  have hb : xs[q].1 = k := by rw [e]; rfl
  have ha : xs[q].2.1 = ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim, Bool.and_eq_true, decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag = some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys = zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => j24 g k i tag ys h
  have hm' : xs[q].2.2.2.1.2 = false := by rw [e]; rfl
  have hn : xs[q].2.2.1.length = ar := by rw [e]; exact one.1
  rw [z297, Bool.and_eq_true]
  refine ⟨one.2, ?_⟩
  split
  · rfl
  · exact e ▸ q12 hq hb ha hm' nd hfl hn (j28 h)
def z19 (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => z87 g k start n ar lo num = true
  | d + 1 => z19 g k start n ar lo (num / 2) d ∧ z19 g k start n ar (lo + num / 2) (num - num / 2) d
theorem q227 {g k start n ar lo num d} (h : z19 g k start n ar lo num d) :
    z87 g k start n ar lo num = true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := z288 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def z20 (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => q148 g k start n ar = true ∧ z19 g k start n ar 0 ar rows
  | d + 1 => z20 g k start (n / 2) ar rows d ∧ z20 g k (start + n / 2) (n - n / 2) ar rows d
theorem z4 {g k start n ar rows d} (h : z20 g k start n ar rows d) :
    z13 g k start n = true := by
  induction d generalizing start n with
  | zero => exact q156 h.1 (q227 h.2)
  | succ d ih =>
    have v := z7 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
theorem q72 (g : Forest) (top : Nat) (prior : Nat → Nat) (hf : g.mode = false)
    (lower : ∀ q, Lower false (varsX q) (z2 q) (prior q))
    (geometry : z84 g prior = true) (rows : z91 g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, z23 (z29 g) k (z52 g k i).toFinset := by
  simp only [z84, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply z117 g 0 i hf (z166 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => z185 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact q1 (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply z117 g _ i hf (z166 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => z185 _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact q1 (rows _ hk) i (by omega) (by omega)
theorem q53 {g top prior k i ws} (hf : g.mode = false)
    (low : ∀ q, Lower false (varsX q) (z2 q) (prior q))
    (geom : z84 g prior = true) (blocks : z91 g top) (le : k ≤ top)
    (idx : z110 g k i ws = true) : z23 (z29 g) k ws.toFinset := by
  simp only [z110, Bool.and_eq_true, decide_eq_true_eq] at idx
  rw [← z99 idx.2]
  exact q72 g top prior hf low geom blocks _ le i idx.1
theorem q68 {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask = m) (hu : g.mode = false) (low : ∀ q, Lower false (varsX q) (z2 q) (prior q))
    (geom : z84 g prior = true) (blocks : z91 g cap)
    (idx : z110 g cap i ws = true) : z23 (z2 m) cap ws.toFinset := by
  subst hm
  exact q53 hu low geom blocks (Nat.le_refl _) idx
theorem j120 : essOK 511 13438558465 = true := by decide +kernel
theorem q19 : vars 511 = inputs := by decide +kernel
theorem q176 : vars 1535 = inputs := by decide +kernel
theorem eg511 : graph = z2 511 := by decide +kernel
theorem q146 : inputs.all z47 = true := by decide +kernel
theorem j30 : bit 0 graph = false := by decide +kernel
theorem z239 {u k S} (run : Live u (z2 511) k S) (sub : ∀ a ∈ S, a ∈ inputs) :
    S = (vars 511).toFinset := by
  have ok := j120
  simp only [essOK, Bool.and_eq_true, beq_iff_eq] at ok
  have sub' : ∀ a ∈ S, a ∈ vars 511 := fun a ha => q19 ▸ sub a ha
  ext a
  rw [List.mem_toFinset]
  refine ⟨sub' a, fun hm => ?_⟩
  obtain ⟨r, s, hd, iso⟩ := z118 ok.1.2 a (List.mem_toFinset.mpr (ok.2 ▸ hm))
  exact z116 run (vars 511) a sub' r s hd iso
theorem z42 (gs : List Gate) (w : List Sig) : (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).length = w.length + (gs.length + 1)
    rw [ih]
    simp
    omega
theorem z43 (a b : List Gate) (w : List Sig) : execute (a ++ b) w = execute b (execute a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons g a ih => exact ih (w ++ [gv w g])
theorem z22 {α : Type} [Inhabited α] (a b : List α) (d : α) (i : Nat) (hi : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
theorem z32 {α : Type} [Inhabited α] (a b : List α) (d : α) (i : Nat) (hi : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]
def z215 : GateOp → Bool
  | .and => true
  | _ => false
theorem z195 (wm : List Sig) (g : Gate) (ia ib : Nat)
    (hinp : g.inputs = [ia, ib]) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    gv wm g = bin (if z215 g.op then 0 else 1) (wm.getD ia zero) (wm.getD ib zero) := by
  apply z67
  intro r
  rcases hop with ha | ho
  · simp [gv, hinp, ha, z215, z121, z139, z104]
  · simp [gv, hinp, ho, z215, z121, z139, z46]
theorem z269 (idx p : Nat) (hp : p < 9 + idx) (preW : List Sig) (hpre : preW.length = 9 + idx)
    (z : Sig) (hz : preW.getD p zero = z) (suf : List Gate) (post : List Sig) :
    ∃ tail : List Sig,
      execute suf (preW ++ [z] ++ post) = preW ++ [z] ++ (post ++ tail) ∧
      execute (suf.map fun g => ⟨g.op, g.inputs.map fun r => if r == 9 + idx then p else if 9 + idx < r then r - 1 else r⟩)
        (preW ++ post) = preW ++ (post ++ tail) := by
  let remap (r : Nat) : Nat := if r == 9 + idx then p else if 9 + idx < r then r - 1 else r
  induction suf generalizing post with
  | nil => exact ⟨[], by simp [execute]⟩
  | cons g suf ih =>
    have get_eq (r : Nat) : (preW ++ post).getD (remap r) zero = (preW ++ [z] ++ post).getD r zero := by
      rcases Nat.lt_trichotomy r (9 + idx) with hr | rfl | hr
      · have hne : (r == 9 + idx) = false := beq_false_of_ne (Nat.ne_of_lt hr)
        have hnot : ¬ (9 + idx < r) := by omega
        have hrm : remap r = r := by simp only [remap, hne, Bool.false_eq_true, if_false, if_neg hnot]
        rw [hrm, List.append_assoc, z22 _ _ _ _ (hpre ▸ hr), z22 _ _ _ _ (hpre ▸ hr)]
      · have hrm : remap (9 + idx) = p := by simp [remap]
        rw [hrm, z22 _ _ _ _ (hpre ▸ hp), hz, List.append_assoc,
            z32 _ _ _ _ (by rw [hpre])]
        simp [hpre]
      · have hne : (r == 9 + idx) = false := beq_false_of_ne (Nat.ne_of_gt hr)
        have hrm : remap r = r - 1 := by simp only [remap, hne, Bool.false_eq_true, if_false, if_pos hr]
        rw [hrm, z32 _ _ _ _ (by rw [hpre]; omega),
            List.append_assoc, z32 _ _ _ _ (by rw [hpre]; omega)]
        rw [hpre]
        have hpos : r - (9 + idx) = (r - 1 - (9 + idx)) + 1 := by omega
        rw [hpos]
        rfl
    have hgv : gv (preW ++ post) ⟨g.op, g.inputs.map remap⟩ = gv (preW ++ [z] ++ post) g := by
      have hxs : List.map (fun x => (preW ++ post).getD (remap x) zero) g.inputs =
          List.map (fun i => (preW ++ [z] ++ post).getD i zero) g.inputs := by
        apply List.map_congr_left
        intro r _
        exact get_eq r
      simp only [gv, List.map_map, Function.comp_def, hxs]
    let v := gv (preW ++ [z] ++ post) g
    obtain ⟨tail, ht1, ht2⟩ := ih (post ++ [v])
    refine ⟨v :: tail, ?_, ?_⟩
    · change execute suf ((preW ++ [z] ++ post) ++ [v]) = _
      simpa only [v, List.append_assoc, List.cons_append, List.nil_append] using ht1
    · change execute (suf.map _) ((preW ++ post) ++ [gv (preW ++ post) ⟨g.op, g.inputs.map remap⟩]) = _
      rw [hgv]
      simpa only [v, List.append_assoc, List.cons_append, List.nil_append] using ht2
theorem q119 (x : Fin 9 → Bool) : ∃ r : Row, sample r = x := by
  let rv := (BitVec.ofBoolListLE (List.ofFn x)).toNat
  have hlt : rv < 512 := by
    have := (BitVec.ofBoolListLE (List.ofFn x)).isLt
    simpa [List.length_ofFn] using this
  refine ⟨⟨rv, hlt⟩, funext fun j => ?_⟩
  change bit ⟨rv, hlt⟩ (inputs.getD j.val zero) = x j
  rw [z56]
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val = x j
  rw [BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.getD_some]
theorem z212 (C : Circuit) (hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
    (hnorm : ∀ i : Fin C.size,
      (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
      (C.gates.get i).inputs.Nodup ∧
      ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1 ∨
       (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2)) :
    (execute C.gates inputs).Nodup := by
  by_contra hnd
  rw [List.nodup_iff_injective_getElem] at hnd
  simp only [Function.Injective, not_forall, not_imp] at hnd
  obtain ⟨a, b, heq, hab⟩ := hnd
  let W := execute C.gates inputs
  have hlen : W.length = 9 + C.gates.length := by
    simpa [W, inputs] using z42 C.gates inputs
  have wlog_pair : ∃ p q, p < q ∧ q < W.length ∧ W.getD p zero = W.getD q zero := by
    have heq' : W.getD a.val zero = W.getD b.val zero := by
      simpa [W, List.getD_eq_getElem?_getD, a.isLt, b.isLt] using heq
    rcases Nat.lt_trichotomy a.val b.val with hlt | hev | hgt
    · exact ⟨a.val, b.val, hlt, b.isLt, heq'⟩
    · exact absurd (Fin.ext hev) hab
    · exact ⟨b.val, a.val, hgt, a.isLt, heq'.symm⟩
  obtain ⟨p, q, hpq, hql, hweq⟩ := wlog_pair
  have hq9 : 9 ≤ q := by
    by_contra hqlt
    obtain ⟨tail, hW⟩ := z77 C.gates inputs
    have ha' : W.getD p zero = inputs.getD p zero := by
      change (execute C.gates inputs).getD p zero = _; rw [hW]; exact z22 _ _ _ _ (by simp [inputs]; omega)
    have hb' : W.getD q zero = inputs.getD q zero := by
      change (execute C.gates inputs).getD q zero = _; rw [hW]; exact z22 _ _ _ _ (by simp [inputs]; omega)
    rw [ha', hb'] at hweq
    have hnd_in := inputs_nodup
    have hpi : inputs[p]'(by simp [inputs]; omega) = inputs[q]'(by simp [inputs]; omega) := by
      simpa [List.getD_eq_getElem?_getD, show p < inputs.length by simp [inputs]; omega,
        show q < inputs.length by simp [inputs]; omega] using hweq
    have heq_idx := (List.nodup_iff_injective_getElem.mp hnd_in)
      (show (fun i : Fin inputs.length => inputs[i.val]) ⟨p, by simp [inputs]; omega⟩ =
        (fun i : Fin inputs.length => inputs[i.val]) ⟨q, by simp [inputs]; omega⟩ from hpi)
    have hval : p = q := congrArg Fin.val heq_idx
    omega
  let idx := q - 9
  have hidx : idx < C.gates.length := by omega
  have hqeq : q = 9 + idx := by omega
  rw [hqeq] at hpq hweq
  let pref := C.gates.take idx
  let g_idx := C.gates[idx]
  let suf := C.gates.drop (idx + 1)
  have hsplit : pref ++ [g_idx] ++ suf = C.gates := by
    simp [pref, g_idx, suf, List.take_append_getElem, List.append_assoc]
  let preW := execute pref inputs
  have hprelen : preW.length = 9 + idx := by
    have : pref.length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
    simpa [preW, this, inputs] using z42 pref inputs
  let z := gv preW g_idx
  let remap (r : Nat) : Nat := if r == 9 + idx then p else if 9 + idx < r then r - 1 else r
  let D : Circuit := ⟨pref ++ suf.map fun g => ⟨g.op, g.inputs.map remap⟩, remap C.output⟩
  have hD_size : D.size < C.size := by
    simp only [Circuit.size, D, pref, suf, List.length_append, List.length_map,
      List.length_take_of_le (Nat.le_of_lt hidx), List.length_drop]
    omega
  have hD_fan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    simp only [D, List.mem_append, List.mem_map] at hg
    rcases hg with hp_mem | ⟨g', hsuf_mem, rfl⟩
    · exact hmin.1 g (List.mem_of_mem_take hp_mem)
    · have hg' := hmin.1 g' (List.mem_of_mem_drop hsuf_mem)
      exact ⟨hg'.1, by simpa using hg'.2⟩
  have hWsplit : W = execute suf (preW ++ [z]) := by
    have : W = execute (pref ++ [g_idx] ++ suf) inputs := congrArg (fun gs => execute gs inputs) hsplit.symm
    rw [z43, z43] at this
    exact this
  have hz_eq : preW.getD p zero = z := by
    obtain ⟨tail', htail'⟩ := z77 suf (preW ++ [z])
    have hp_val : W.getD p zero = preW.getD p zero := by
      rw [hWsplit, htail', List.append_assoc]
      exact z22 _ _ _ _ (by rw [hprelen]; exact hpq)
    have hq_val : W.getD (9 + idx) zero = z := by
      rw [hWsplit, htail']
      rw [z22 _ _ _ _ (by simp [hprelen]), z32 _ _ _ _ (by rw [hprelen])]
      simp [hprelen]
    rw [← hp_val, ← hq_val, hweq]
  obtain ⟨tail, hWtail, hDtail⟩ := z269 idx p hpq preW hprelen z hz_eq suf []
  have hW_eq : W = preW ++ [z] ++ tail := by simpa [hWsplit] using hWtail
  have hD_eq : execute D.gates inputs = preW ++ tail := by
    simpa only [D, preW, remap, z43, List.append_nil, List.nil_append] using hDtail
  have hD_out : (execute D.gates inputs).getD D.output zero = W.getD C.output zero := by
    rw [hD_eq, hW_eq]
    change (preW ++ tail).getD (remap C.output) zero = (preW ++ [z] ++ tail).getD C.output zero
    rcases Nat.lt_trichotomy C.output (9 + idx) with hr | hr | hr
    · have hne : (C.output == 9 + idx) = false := beq_false_of_ne (Nat.ne_of_lt hr)
      have hnot : ¬ (9 + idx < C.output) := by omega
      have hrm : remap C.output = C.output := by simp only [remap, hne, Bool.false_eq_true, if_false, if_neg hnot]
      rw [hrm, List.append_assoc, z22 _ _ _ _ (hprelen ▸ hr), z22 _ _ _ _ (hprelen ▸ hr)]
    · have hrm : remap C.output = p := by simp [remap, hr]
      rw [hrm, hr, z22 _ _ _ _ (hprelen ▸ hpq), hz_eq,
          List.append_assoc, z32 _ _ _ _ (by rw [hprelen])]
      simp [hprelen]
    · have hne : (C.output == 9 + idx) = false := beq_false_of_ne (Nat.ne_of_gt hr)
      have hrm : remap C.output = C.output - 1 := by simp only [remap, hne, Bool.false_eq_true, if_false, if_pos hr]
      rw [hrm, z32 _ _ _ _ (by rw [hprelen]; omega),
          List.append_assoc, z32 _ _ _ _ (by rw [hprelen]; omega), hprelen]
      have hpos : C.output - (9 + idx) = (C.output - 1 - (9 + idx)) + 1 := by omega
      rw [hpos]
      rfl
  have hD_fun : PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C := by
    funext x
    obtain ⟨r, hr⟩ := q119 x
    rw [← hr]
    change (D.wires (List.ofFn (sample r))).getD D.output false = (C.wires (List.ofFn (sample r))).getD C.output false
    rw [← z190 D hD_fan D.output r, ← z190 C hmin.1 C.output r, hD_out]
  have hle := hmin.2 D hD_fan hD_fun
  omega
theorem q147 : ∀ b ∈ inputs, bit 0 b = false ∧ bit ⟨511, by decide⟩ b = true := by
  have key : ∀ fj : Fin 9,
      bit 0 (inputs.getD fj.val zero) = false ∧ bit ⟨511, by decide⟩ (inputs.getD fj.val zero) = true := by
    intro fj
    have c0 := z56 fj 0
    have c1 := z56 fj ⟨511, by decide⟩
    change bit 0 (inputs.getD fj.val zero) = _ at c0
    change bit ⟨511, by decide⟩ (inputs.getD fj.val zero) = _ at c1
    rw [c0, c1]
    refine ⟨Nat.zero_testBit _, ?_⟩
    fin_cases fj <;> decide
  intro b hb
  obtain ⟨j, hj, hbj⟩ := List.getElem_of_mem hb
  have hj9 : j < 9 := by simpa [inputs] using hj
  have hbj' : b = inputs.getD j zero := by rw [← hbj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [hbj']
  exact key ⟨j, hj9⟩
theorem z177 (C : Circuit)
    (hGate : ∀ i : Fin C.size, (C.gates.get i).inputs.length = 2 ∧
      (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
      ((C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.or)) :
    ∀ m ≤ C.size, ∀ a ∈ execute (C.gates.take m) inputs,
      bit 0 a = false ∧ bit ⟨511, by decide⟩ a = true ∧
      ∀ r s : Row, (r.val &&& s.val = r.val) → bit r a = true → bit s a = true := by
  intro m hm
  induction m with
  | zero =>
    intro a ha
    change a ∈ inputs at ha
    have hin := q147
    refine ⟨(hin a ha).1, (hin a ha).2, fun r s hrs hra => ?_⟩
    obtain ⟨j, hj, haj⟩ := List.getElem_of_mem ha
    have hle9 : j < 9 := by simpa [inputs] using hj
    have haj' : a = inputs.getD j zero := by rw [← haj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [haj'] at hra ⊢
    have hb1 := z56 ⟨j, hle9⟩ r
    have hb2 := z56 ⟨j, hle9⟩ s
    change bit r (inputs.getD (⟨j, hle9⟩ : Fin 9).val zero) = _ at hb1
    change bit s (inputs.getD (⟨j, hle9⟩ : Fin 9).val zero) = _ at hb2
    rw [hb1] at hra
    rw [hb2]
    have htb := congrArg (fun n => n.testBit j) hrs
    rw [Nat.testBit_and] at htb
    dsimp only at hra ⊢
    rw [hra] at htb
    simpa using htb
  | succ m ih =>
    have hm_lt : m < C.size := by omega
    have hm_lt' : m < C.gates.length := hm_lt
    have ih' := ih (Nat.le_of_lt hm_lt)
    rw [List.take_succ_eq_append_getElem hm_lt', z43]
    let gm := C.gates.get ⟨m, hm_lt⟩
    let wm := execute (C.gates.take m) inputs
    have hwm_len : wm.length = 9 + m := by
      simp [wm, z42, inputs, List.length_take_of_le (Nat.le_of_lt hm_lt)]
    change ∀ a ∈ wm ++ [gv wm gm], _
    intro a ha
    rcases List.mem_append.mp ha with haw | haz
    · exact ih' a haw
    · simp only [List.mem_singleton] at haz
      subst a
      obtain ⟨hlen2, hltm, hop⟩ := hGate ⟨m, hm_lt⟩
      obtain ⟨ia, ib, hinp⟩ := List.length_eq_two.mp hlen2
      have hia_mem : wm.getD ia zero ∈ wm := by
        have hlt_ia : ia < wm.length := by rw [hwm_len]; exact hltm ia (by simp [hinp])
        simp [List.getD_eq_getElem?_getD, hlt_ia]
      have hib_mem : wm.getD ib zero ∈ wm := by
        have hlt_ib : ib < wm.length := by rw [hwm_len]; exact hltm ib (by simp [hinp])
        simp [List.getD_eq_getElem?_getD, hlt_ib]
      obtain ⟨ia0, ia511, iamono⟩ := ih' _ hia_mem
      obtain ⟨ib0, ib511, ibmono⟩ := ih' _ hib_mem
      have hbin := z195 wm gm ia ib hinp hop
      rw [hbin]
      rcases hop with h_and | h_or
      · have hd0 : (if z215 gm.op then 0 else 1) = 0 := by
          have hgm : gm.op = GateOp.and := h_and
          rw [hgm]
          rfl
        rw [hd0]
        have hba (r : Row) : bit r (bin 0 (wm.getD ia zero) (wm.getD ib zero)) =
            (bit r (wm.getD ia zero) && bit r (wm.getD ib zero)) := BitVec.getLsbD_and
        refine ⟨by rw [hba, ia0, ib0]; rfl, by rw [hba, ia511, ib511]; rfl, fun r s hrs hra => ?_⟩
        rw [hba, Bool.and_eq_true] at hra ⊢
        exact ⟨iamono r s hrs hra.1, ibmono r s hrs hra.2⟩
      · have hd1 : (if z215 gm.op then 0 else 1) = 1 := by
          have hgm : gm.op = GateOp.or := h_or
          rw [hgm]
          rfl
        rw [hd1]
        have hbo (r : Row) : bit r (bin 1 (wm.getD ia zero) (wm.getD ib zero)) =
            (bit r (wm.getD ia zero) || bit r (wm.getD ib zero)) := BitVec.getLsbD_or
        refine ⟨by rw [hbo, ia0, ib0]; rfl, by rw [hbo, ia511, ib511]; rfl, fun r s hrs hra => ?_⟩
        rw [hbo, Bool.or_eq_true] at hra ⊢
        rcases hra with hra | hra
        · exact Or.inl (iamono r s hrs hra)
        · exact Or.inr (ibmono r s hrs hra)
theorem z170 (a : Sig) (h0 : bit 0 a = false) (h511 : bit ⟨511, by decide⟩ a = true) :
    proper a := by
  refine ⟨fun hz => ?_, fun ho => ?_⟩
  · have := congrArg (bit ⟨511, by decide⟩) hz
    rw [h511, z46] at this
    exact Bool.noConfusion this
  · have := congrArg (bit 0) ho
    rw [h0, z104] at this
    exact Bool.noConfusion this
theorem q15 (C : Circuit) (hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
    (hfun : PEqualNP.MetaComplexity.circuitFun 9 C = edge)
    (hGate : ∀ i : Fin C.size, (C.gates.get i).inputs.length = 2 ∧
      (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
      ((C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.or))
    (v : Fin 9) (hv : v ∈ ([4, 6, 7] : List (Fin 9))) (i : Fin C.size) (w : Nat)
    (hw_lt : w < 9 + i.val) (hw_ne : w ≠ v.val) (hor : (C.gates.get i).op = GateOp.or)
    (hinp : (C.gates.get i).inputs = [v.val, w] ∨ (C.gates.get i).inputs = [w, v.val])
    (huniq : ∀ k : Fin C.size, k ≠ i → v.val ∉ (C.gates.get k).inputs) :
    let wv := (execute C.gates inputs).getD w zero
    wv ∉ inputs ∧ (wv &&& unitMask) = zero ∧ (wv &&& z39 v.val) = zero := by
  let W := execute C.gates inputs
  let wv := W.getD w zero
  let flipV (r : Row) : Row := ⟨r.val ^^^ (1 <<< v.val), q18 r v⟩
  have hindep : ∀ m ≤ i.val, ∀ t < 9 + m, t ≠ v.val → ∀ r : Row,
      bit r ((execute (C.gates.take m) inputs).getD t zero) =
      bit (flipV r) ((execute (C.gates.take m) inputs).getD t zero) := by
    intro m hm
    induction m with
    | zero =>
      intro t ht9 htne r
      simp only [Nat.add_zero] at ht9
      change bit r (inputs.getD t zero) = bit (flipV r) (inputs.getD t zero)
      have hb1 := z56 ⟨t, ht9⟩ r
      have hb2 := z56 ⟨t, ht9⟩ (flipV r)
      change bit r (inputs.getD (⟨t, ht9⟩ : Fin 9).val zero) = _ at hb1
      change bit (flipV r) (inputs.getD (⟨t, ht9⟩ : Fin 9).val zero) = _ at hb2
      rw [hb1, hb2]
      exact (q10 r ⟨t, ht9⟩ v (fun e => htne (congrArg Fin.val e))).symm
    | succ m ih =>
      have hm_lt : m < C.size := by omega
      have hm_lt' : m < C.gates.length := hm_lt
      have ih' := ih (by omega)
      rw [List.take_succ_eq_append_getElem hm_lt', z43]
      let gm := C.gates.get ⟨m, hm_lt⟩
      let wm := execute (C.gates.take m) inputs
      have hwm_len : wm.length = 9 + m := by
        simp [wm, z42, inputs, List.length_take_of_le (Nat.le_of_lt hm_lt)]
      intro t ht_lt ht_ne r
      change bit r ((wm ++ [gv wm gm]).getD t zero) = bit (flipV r) ((wm ++ [gv wm gm]).getD t zero)
      rcases Nat.lt_or_eq_of_le (show t ≤ 9 + m from by omega) with ht_old | rfl
      · rw [z22 _ _ _ _ (by rw [hwm_len]; exact ht_old)]
        exact ih' t ht_old ht_ne r
      · rw [z32 _ _ _ _ (by rw [hwm_len]), hwm_len, Nat.sub_self]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
        have hm_ne : (⟨m, hm_lt⟩ : Fin C.size) ≠ i := by
          intro e
          have hmv : m = i.val := congrArg Fin.val e
          omega
        have hv_not : v.val ∉ gm.inputs := huniq ⟨m, hm_lt⟩ hm_ne
        have hgm_fan : gm.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := (hmin.1 gm (C.gates.get_mem _)).1
        have harg : gm.inputs.map (fun p => (wm.map (bit r)).getD p false) =
                    gm.inputs.map (fun p => (wm.map (bit (flipV r))).getD p false) := by
          apply List.map_congr_left
          intro p hp
          simp only [q251]
          have hp_lt := (hGate ⟨m, hm_lt⟩).2.1 p hp
          exact ih' p hp_lt (fun he => hv_not (he ▸ hp)) r
        rw [z286 r gm wm hgm_fan, z286 (flipV r) gm wm hgm_fan, harg]
  have hw_agree (r : Row) : bit r wv = bit (flipV r) wv := by
    have hW_split : execute C.gates inputs = execute (C.gates.drop i.val) (execute (C.gates.take i.val) inputs) := by
      conv_lhs => rw [← List.take_append_drop i.val C.gates]
      exact z43 _ _ _
    have hex : ∃ tail, W = execute (C.gates.take i.val) inputs ++ tail := by
      change ∃ tail, execute C.gates inputs = _
      rw [hW_split]
      exact z77 _ _
    obtain ⟨tail, htail⟩ := hex
    have hlen_i : (execute (C.gates.take i.val) inputs).length = 9 + i.val := by
      simp [z42, inputs, List.length_take_of_le (Nat.le_of_lt i.isLt)]
    have heqw : wv = (execute (C.gates.take i.val) inputs).getD w zero := by
      change W.getD w zero = _
      rw [htail, z22 _ _ _ _ (by rw [hlen_i]; exact hw_lt)]
    rw [heqw]
    exact hindep i.val (Nat.le_refl _) w hw_lt hw_ne r
  have hforb : (wv &&& z39 v.val) = zero := by
    apply z67
    intro r
    rw [z46, show bit r (wv &&& z39 v.val) = (bit r wv && bit r (z39 v.val)) from BitVec.getLsbD_and]
    cases hm_bit : bit r (z39 v.val)
    · simp
    · suffices bit r wv = false by simp [this]
      by_contra hwt
      have hwt' : bit r wv = true := Bool.eq_true_of_not_eq_false hwt
      have hwf : bit (flipV r) wv = true := (hw_agree r).symm.trans hwt'
      obtain ⟨_, hg0, hg1⟩ := z254 v hv r hm_bit
      have hprop_ge : ∀ m, i.val < m → m ≤ C.size → ∀ t < 9 + m, t ≠ v.val →
          bit r ((execute (C.gates.take m) inputs).getD t zero) =
          bit (flipV r) ((execute (C.gates.take m) inputs).getD t zero) := by
        intro m him
        induction m with
        | zero => omega
        | succ m ih =>
          intro hm_le
          have hm_lt : m < C.size := by omega
          have hm_lt' : m < C.gates.length := hm_lt
          rw [List.take_succ_eq_append_getElem hm_lt', z43]
          let gm := C.gates.get ⟨m, hm_lt⟩
          let wm := execute (C.gates.take m) inputs
          have hwm_len : wm.length = 9 + m := by
            simp [wm, z42, inputs, List.length_take_of_le (Nat.le_of_lt hm_lt)]
          by_cases hmi : m = i.val
          · subst m
            intro t ht_lt ht_ne
            change bit r ((wm ++ [gv wm gm]).getD t zero) = bit (flipV r) ((wm ++ [gv wm gm]).getD t zero)
            rcases Nat.lt_or_eq_of_le (show t ≤ 9 + i.val from by omega) with ht_old | rfl
            · rw [z22 _ _ _ _ (by rw [hwm_len]; exact ht_old)]
              exact hindep i.val (Nat.le_refl _) t ht_old ht_ne r
            · rw [z32 _ _ _ _ (by rw [hwm_len]), hwm_len, Nat.sub_self]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
              have hW_split' : execute C.gates inputs = execute (C.gates.drop i.val) (execute (C.gates.take i.val) inputs) := by
                conv_lhs => rw [← List.take_append_drop i.val C.gates]
                exact z43 _ _ _
              have hex_i : ∃ tail, W = wm ++ tail := by
                change ∃ tail, execute C.gates inputs = wm ++ tail
                rw [hW_split']
                exact z77 _ _
              obtain ⟨tail, htail⟩ := hex_i
              have hwi_w : wm.getD w zero = wv := by
                change _ = W.getD w zero
                rw [htail, z22 _ _ _ _ (by rw [hwm_len]; exact hw_lt)]
              have hd1 : (if z215 gm.op then 0 else 1) = 1 := by
                have hgm : gm.op = GateOp.or := hor
                rw [hgm]
                rfl
              have hgv_side (q : Row) (hq : bit q wv = true) : bit q (gv wm gm) = true := by
                have hbo (x y : Sig) : bit q (bin 1 x y) = (bit q x || bit q y) := BitVec.getLsbD_or
                rcases hinp with hvw | hwv
                · rw [z195 wm gm v.val w hvw (Or.inr hor), hd1, hbo, hwi_w, hq]
                  simp
                · rw [z195 wm gm w v.val hwv (Or.inr hor), hd1, hbo, hwi_w, hq]
                  simp
              rw [hgv_side r hwt', hgv_side (flipV r) hwf]
          · have ih' := ih (by omega) (by omega)
            intro t ht_lt ht_ne
            change bit r ((wm ++ [gv wm gm]).getD t zero) = bit (flipV r) ((wm ++ [gv wm gm]).getD t zero)
            rcases Nat.lt_or_eq_of_le (show t ≤ 9 + m from by omega) with ht_old | rfl
            · rw [z22 _ _ _ _ (by rw [hwm_len]; exact ht_old)]
              exact ih' t ht_old ht_ne
            · rw [z32 _ _ _ _ (by rw [hwm_len]), hwm_len, Nat.sub_self]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
              have hm_ne : (⟨m, hm_lt⟩ : Fin C.size) ≠ i := by intro e; exact hmi (congrArg Fin.val e)
              have hv_not : v.val ∉ gm.inputs := huniq ⟨m, hm_lt⟩ hm_ne
              have hgm_fan : gm.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := (hmin.1 gm (C.gates.get_mem _)).1
              have harg : gm.inputs.map (fun p => (wm.map (bit r)).getD p false) =
                          gm.inputs.map (fun p => (wm.map (bit (flipV r))).getD p false) := by
                apply List.map_congr_left
                intro p hp
                simp only [q251]
                have hp_lt := (hGate ⟨m, hm_lt⟩).2.1 p hp
                exact ih' p hp_lt (fun he => hv_not (he ▸ hp))
              rw [z286 r gm wm hgm_fan, z286 (flipV r) gm wm hgm_fan, harg]
      have hgoalEq : W.getD C.output zero = graph := by
        apply z67
        intro q
        exact (z190 C hmin.1 C.output q).trans ((congrFun hfun (sample q)).trans (q42 q).symm)
      have hout_ne : C.output ≠ v.val := by
        intro heq_out
        obtain ⟨q, hq⟩ := z135 v
        obtain ⟨tail, hW⟩ := z77 C.gates inputs
        have hin_v : W.getD v.val zero = inputs.getD v.val zero := by
          change (execute C.gates inputs).getD v.val zero = _
          rw [hW]
          exact z22 _ _ _ _ (by simp [inputs])
        rw [← hgoalEq, heq_out, hin_v] at hq
        exact hq rfl
      have h_agree_all : bit r (W.getD C.output zero) = bit (flipV r) (W.getD C.output zero) := by
        by_cases hlt : C.output < 9 + C.size
        · have heqC := hprop_ge C.size i.isLt (Nat.le_refl _) C.output hlt hout_ne
          simpa [W, Circuit.size, List.take_length] using heqC
        · have hlenW : W.length ≤ C.output := by
            have := z42 C.gates inputs
            change (execute C.gates inputs).length ≤ C.output
            rw [z42]
            simp [Circuit.size, inputs] at hlt ⊢
            omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlenW, z46]
      have hflip_eq : flipV r = Fin.ofNat 512 (r.val ^^^ (1 <<< v.val)) :=
        Fin.ext (by simp [flipV, Nat.mod_eq_of_lt (q18 r v)])
      rw [hgoalEq, hflip_eq, hg0, hg1] at h_agree_all
      exact Bool.noConfusion h_agree_all
  have hunit : (wv &&& unitMask) = zero := by
    apply z67
    intro r
    rw [z46, show bit r (wv &&& unitMask) = (bit r wv && bit r unitMask) from BitVec.getLsbD_and]
    cases hu_bit : bit r unitMask
    · simp
    · suffices bit r wv = false by simp [this]
      by_contra hwt
      have hwt' : bit r wv = true := Bool.eq_true_of_not_eq_false hwt
      have hur := z271 r ▸ hu_bit
      simp only [List.any_eq_true, List.mem_finRange, decide_eq_true_eq, true_and] at hur
      obtain ⟨u, hr_val⟩ := hur
      have hw_mem : wv ∈ W := by
        have hlenW : w < W.length := by
          have := i.isLt
          change w < (execute C.gates inputs).length
          rw [z42]
          simp [Circuit.size, inputs] at this ⊢
          omega
        change W.getD w zero ∈ W
        simp [List.getD_eq_getElem?_getD, hlenW]
      have hprops := z177 C hGate C.size (Nat.le_refl _) wv (by simpa [W, Circuit.size, List.take_length] using hw_mem)
      by_cases huv : u = v
      · subst u
        have h0eq : bit r wv = bit (flipV ⟨0, by decide⟩) wv := by
          have hr_eq : r = flipV ⟨0, by decide⟩ := Fin.ext (by simp [flipV, hr_val])
          rw [hr_eq]
        rw [h0eq, ← hw_agree ⟨0, by decide⟩] at hwt'
        change bit (0 : Row) wv = true at hwt'
        rw [hprops.1] at hwt'
        exact Bool.noConfusion hwt'
      · obtain ⟨r', hrm, hr_sub⟩ := z218 v hv u huv
        have hr_le : r.val &&& r'.val = r.val := by rw [hr_val, Nat.and_comm]; exact hr_sub
        have hr'_true := hprops.2.2 r r' hr_le hwt'
        have hz := congrArg (bit r') hforb
        rw [show bit r' (wv &&& z39 v.val) = (bit r' wv && bit r' (z39 v.val)) from BitVec.getLsbD_and,
          z46, hr'_true, hrm] at hz
        exact Bool.noConfusion hz
  have hnot_in : wv ∉ inputs := by
    intro hm
    obtain ⟨u, hu, heq⟩ := List.getElem_of_mem hm
    have hu9 : u < 9 := by simpa [inputs] using hu
    let r0 : Row := Fin.ofNat 512 (1 <<< u)
    have hb1 : bit r0 wv = true := by
      have hwu : wv = inputs.getD u zero := by rw [← heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]; rfl
      rw [hwu]
      exact z296 ⟨u, hu9⟩
    have hb2 : bit r0 unitMask = true := q159 ⟨u, hu9⟩
    have hz := congrArg (bit r0) hunit
    rw [show bit r0 (wv &&& unitMask) = (bit r0 wv && bit r0 unitMask) from BitVec.getLsbD_and,
      z46, hb1, hb2] at hz
    exact Bool.noConfusion hz
  exact ⟨hnot_in, hunit, hforb⟩
theorem j25 (C : Circuit) (hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
    (hfun : PEqualNP.MetaComplexity.circuitFun 9 C = edge)
    (hnorm : ∀ i : Fin C.size,
      (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
      (C.gates.get i).inputs.Nodup ∧
      ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1 ∨
       (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2))
    (hS : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
      ({i : Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card = 1 ∧
      ∀ i ∈ ({i : Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)), (C.gates.get i).op = GateOp.or)
    (hndW : (execute C.gates inputs).Nodup)
    (hGate : ∀ i : Fin C.size, (C.gates.get i).inputs.length = 2 ∧
      (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
      ((C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.or)) :
    ∀ gs pref : List Gate, pref ++ gs = C.gates →
      graph ∈ execute gs (execute pref inputs) →
      ∃ k S, k ≤ gs.length ∧ Live467 graph k S ∧ (∀ a ∈ S, a ∈ execute pref inputs) ∧
        ∀ v ∈ ([4, 6, 7] : List (Fin 9)), inputs.getD v.val zero ∈ S → ∃ j : Fin gs.length, v.val ∈ (gs.get j).inputs := by
  intro gs
  induction gs with
  | nil =>
    intro pref _ hmem
    change graph ∈ execute [] (execute pref inputs) at hmem
    change graph ∈ execute pref inputs at hmem
    refine ⟨0, {graph}, by omega, Live467.stop z132, fun a ha => ?_, fun v _ hvS => ?_⟩
    · simpa [Finset.mem_singleton.mp ha] using hmem
    · simp only [Finset.mem_singleton] at hvS
      obtain ⟨r, hr⟩ := z135 v
      exact False.elim (hr (congrArg (bit r) hvS.symm))
  | cons g gs ih =>
    intro pref hsplit hmem
    let m := pref.length
    have hm_lt : m < C.size := by
      have := congrArg List.length hsplit
      simp only [Circuit.size, List.length_append, List.length_cons] at this ⊢
      omega
    have hpref_take : pref = C.gates.take m := by
      have h := congrArg (List.take m) hsplit
      simpa [m, List.take_left] using h
    have hg_eq : g = C.gates.get ⟨m, hm_lt⟩ := by
      have h := congrArg (fun l => l[m]?) hsplit
      have hg1 : (pref ++ g :: gs)[m]? = some g := by simp [m]
      have hg2 : C.gates[m]? = some (C.gates.get ⟨m, hm_lt⟩) := by simp [hm_lt]
      rw [hg1, hg2] at h
      exact Option.some.inj h
    let pref' := pref ++ [g]
    have hsplit' : pref' ++ gs = C.gates := by simpa [pref', List.append_assoc] using hsplit
    have hexec' : execute pref' inputs = execute pref inputs ++ [gv (execute pref inputs) g] := by
      simp [pref', z43, execute]
    have hmem' : graph ∈ execute gs (execute pref' inputs) := by
      rw [hexec']
      exact hmem
    obtain ⟨k, S, hk, hlive, hsub, h4⟩ := ih pref' hsplit' hmem'
    rw [hexec'] at hsub
    let wm := execute pref inputs
    let z := gv wm g
    by_cases hzS : z ∈ S
    · obtain ⟨tail, hW⟩ : ∃ tail, execute C.gates inputs = wm ++ ([z] ++ tail) := by
        have hst : execute C.gates inputs = execute gs (wm ++ [z]) := by
          rw [← hsplit, z43]
          rfl
        obtain ⟨tail, ht⟩ := z77 gs (wm ++ [z])
        exact ⟨tail, by rw [hst, ht, List.append_assoc]⟩
      have hnd_wm : wm.Nodup := (List.nodup_append.mp (hW ▸ hndW)).1
      have hz_not_wm : z ∉ wm := fun hm => (List.nodup_append.mp (hW ▸ hndW)).2.2 z hm z List.mem_cons_self rfl
      have wm_len : wm.length = 9 + m := by simp [wm, z42, inputs, m]
      have hwm_ext : ∃ l, wm = inputs ++ l := z77 pref inputs
      have idx_of_input (idx : Nat) (hidx : idx < wm.length) (v : Fin 9)
          (heq : wm.getD idx zero = inputs.getD v.val zero) : idx = v.val := by
        obtain ⟨l, hl⟩ := hwm_ext
        have hv_lt : v.val < wm.length := by rw [wm_len]; have := v.isLt; omega
        have hin_wm : wm.getD v.val zero = inputs.getD v.val zero := by
          rw [hl]; exact z22 _ _ _ _ (by simp [inputs])
        rw [← hin_wm] at heq
        have hgi : wm[idx]'hidx = wm[v.val]'hv_lt := by
          simpa [List.getD_eq_getElem?_getD, hidx, hv_lt] using heq
        exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd_wm)
          (show (fun k : Fin wm.length => wm[k.val]) ⟨idx, hidx⟩ =
            (fun k : Fin wm.length => wm[k.val]) ⟨v.val, hv_lt⟩ from hgi))
      obtain ⟨hlen2, hltm, hop⟩ := hg_eq ▸ hGate ⟨m, hm_lt⟩
      have hg_nd : g.inputs.Nodup := hg_eq ▸ (hnorm ⟨m, hm_lt⟩).2.1
      obtain ⟨ia, ib, hinp⟩ := List.length_eq_two.mp hlen2
      have hia_ne_ib : ia ≠ ib := by simpa [hinp] using hg_nd
      have hia_lt : ia < wm.length := by rw [wm_len]; exact hltm ia (by simp [hinp])
      have hib_lt : ib < wm.length := by rw [wm_len]; exact hltm ib (by simp [hinp])
      let d := if z215 g.op then 0 else 1
      let a := wm.getD ia zero
      let b := wm.getD ib zero
      have hz_bin : z = bin d a b := z195 wm g ia ib hinp hop
      have hd : allowed false d := by dsimp [d]; split <;> exact Or.inl (by omega)
      have ha_mem : a ∈ wm := by change wm.getD ia zero ∈ wm; simp [List.getD_eq_getElem?_getD, hia_lt]
      have hb_mem : b ∈ wm := by change wm.getD ib zero ∈ wm; simp [List.getD_eq_getElem?_getD, hib_lt]
      have hw_props : ∀ w ∈ wm, bit 0 w = false ∧ bit ⟨511, by decide⟩ w = true ∧
          ∀ r s : Row, (r.val &&& s.val = r.val) → bit r w = true → bit s w = true := by
        simpa [wm, hpref_take] using z177 C hGate m (Nat.le_of_lt hm_lt)
      have ha_p : proper a := z170 a (hw_props a ha_mem).1 (hw_props a ha_mem).2.1
      have hb_p : proper b := z170 b (hw_props b hb_mem).1 (hw_props b hb_mem).2.1
      have hab : a ≠ b := by
        intro hab_eq
        have hgi : wm[ia]'hia_lt = wm[ib]'hib_lt := by
          simpa [a, b, List.getD_eq_getElem?_getD, hia_lt, hib_lt] using hab_eq
        exact hia_ne_ib (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd_wm)
          (show (fun k : Fin wm.length => wm[k.val]) ⟨ia, hia_lt⟩ =
            (fun k : Fin wm.length => wm[k.val]) ⟨ib, hib_lt⟩ from hgi)))
      let U := S.erase z
      have hU_sub : ∀ y ∈ U, y ∈ wm := by
        intro y hy
        obtain ⟨hne, hyS⟩ := Finset.mem_erase.mp hy
        rcases List.mem_append.mp (hsub y hyS) with hyw | hyz
        · exact hyw
        · exact False.elim (hne (by simpa using hyz))
      have hfresh : bin d a b ∉ insert a (insert b U) := by
        rw [← hz_bin]
        intro hm_in
        rcases Finset.mem_insert.mp hm_in with e | hm_in
        · exact hz_not_wm (e ▸ ha_mem)
        · rcases Finset.mem_insert.mp hm_in with e | hm_in
          · exact hz_not_wm (e ▸ hb_mem)
          · exact hz_not_wm (hU_sub _ hm_in)
      have check_side (ix iy : Nat) (hix : ix < wm.length) (hiy : iy < wm.length)
          (hne_i : ix ≠ iy) (hinp_pair : g.inputs = [ix, iy] ∨ g.inputs = [iy, ix]) :
          let x := wm.getD ix zero
          let y := wm.getD iy zero
          z88 x y d (decide (x ∈ U)) = true := by
        intro x y
        by_cases hx467 : is467 x = true
        · have hvx : ∃ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) ∧ x = inputs.getD v.val zero := by
            simp only [is467, Bool.or_eq_true, beq_iff_eq] at hx467
            rcases hx467 with (e | e) | e
            · exact ⟨4, by simp, e⟩
            · exact ⟨6, by simp, e⟩
            · exact ⟨7, by simp, e⟩
          obtain ⟨v, hv, hxv⟩ := hvx
          have hix_eq : ix = v.val := idx_of_input ix hix v hxv
          have hv_mem_g : v.val ∈ (C.gates.get ⟨m, hm_lt⟩).inputs := by
            rw [← hg_eq, ← hix_eq]
            rcases hinp_pair with h1 | h2
            · simp [h1]
            · simp [h2]
          obtain ⟨hcard1, hall_or⟩ := hS v hv
          let readers : Finset (Fin C.size) := Finset.univ.filter fun j => v.val ∈ (C.gates.get j).inputs
          have hmem_r : (⟨m, hm_lt⟩ : Fin C.size) ∈ readers := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_mem_g⟩
          have hreaders_eq : readers = {⟨m, hm_lt⟩} := by
            obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hcard1
            have hm0 : (⟨m, hm_lt⟩ : Fin C.size) = r0 := Finset.mem_singleton.mp (hr0 ▸ hmem_r)
            exact hm0 ▸ hr0
          have hor_m : (C.gates.get ⟨m, hm_lt⟩).op = GateOp.or := hall_or ⟨m, hm_lt⟩ hmem_r
          have hd1 : d = 1 := by dsimp [d]; rw [hg_eq, hor_m]; rfl
          have huniq : ∀ k : Fin C.size, k ≠ ⟨m, hm_lt⟩ → v.val ∉ (C.gates.get k).inputs := by
            intro k hne hmemk
            have : k ∈ readers := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmemk⟩
            rw [hreaders_eq, Finset.mem_singleton] at this
            exact hne this
          have hx_not_U : x ∉ U := by
            intro hxU
            have hxS : inputs.getD v.val zero ∈ S := hxv ▸ Finset.mem_of_mem_erase hxU
            obtain ⟨j, hj⟩ := h4 v hv hxS
            have hj_lt : m + 1 + j.val < C.size := by
              have := congrArg List.length hsplit
              simp only [Circuit.size, List.length_append, List.length_cons] at this ⊢
              omega
            have hj_eq : gs.get j = C.gates.get ⟨m + 1 + j.val, hj_lt⟩ := by
              have h := congrArg (fun l => l[m + 1 + j.val]?) hsplit
              have h1 : (pref ++ g :: gs)[m + 1 + j.val]? = some (gs.get j) := by
                have hex_j : m + 1 + j.val = (pref ++ [g]).length + j.val := by simp [m]
                rw [show pref ++ g :: gs = (pref ++ [g]) ++ gs by simp, hex_j, List.getElem?_append_right (by omega)]
                simp [j.isLt]
              have h2 : C.gates[m + 1 + j.val]? = some (C.gates.get ⟨m + 1 + j.val, hj_lt⟩) := by simp [hj_lt]
              rw [h1, h2] at h
              exact Option.some.inj h
            have hv_later : v.val ∈ (C.gates.get ⟨m + 1 + j.val, hj_lt⟩).inputs := hj_eq ▸ hj
            exact huniq ⟨m + 1 + j.val, hj_lt⟩ (by intro e; have : m + 1 + j.val = m := congrArg Fin.val e; omega) hv_later
          have hiy_lt_m : iy < 9 + m := by rw [← wm_len]; exact hiy
          have hiy_ne_v : iy ≠ v.val := hix_eq ▸ hne_i.symm
          have hinp_v : (C.gates.get ⟨m, hm_lt⟩).inputs = [v.val, iy] ∨ (C.gates.get ⟨m, hm_lt⟩).inputs = [iy, v.val] := by
            rw [← hg_eq, ← hix_eq]; exact hinp_pair
          obtain ⟨hnot_in, hunit, hforb⟩ := q15 C hmin hfun hGate v hv ⟨m, hm_lt⟩ iy hiy_lt_m hiy_ne_v hor_m hinp_v huniq
          have hy_eq_W : y = (execute C.gates inputs).getD iy zero := by
            change wm.getD iy zero = _; rw [hW, z22 _ _ _ _ hiy]
          have hmask_x : z54 x = z39 v.val := by rw [hxv]; exact q59 v hv
          have hx_dec : decide (x ∈ U) = false := decide_eq_false hx_not_U
          simp only [z88, hx467, ↓reduceIte, hd1, beq_self_eq_true, hx_dec, Bool.not_false, Bool.true_and,
            z109, List.contains_eq_mem, decide_eq_true_eq, hy_eq_W, hnot_in, decide_false, hmask_x, hunit, hforb]
        · simp [z88, hx467]
      have hok : ok467 U a b d := by
        simp only [ok467, z31, Bool.and_eq_true]
        exact ⟨check_side ia ib hia_lt hib_lt hia_ne_ib (Or.inl hinp),
               check_side ib ia hib_lt hia_lt hia_ne_ib.symm (Or.inr hinp)⟩
      have hS_eq : insert z U = S := Finset.insert_erase hzS
      have hlive' := Live467.binary hd hok ha_p hb_p hab hfresh (by rw [← hz_bin, hS_eq]; exact hlive)
      refine ⟨k + 1, insert a (insert b U), by simp [hk], hlive', fun y hy => ?_, fun v hv hv_in => ?_⟩
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ha_mem
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hb_mem
          · exact hU_sub y hy
      · rcases Finset.mem_insert.mp hv_in with e | hv_in
        · have hidx := idx_of_input ia hia_lt v e.symm
          exact ⟨⟨0, by simp⟩, by simp [hinp, hidx]⟩
        · rcases Finset.mem_insert.mp hv_in with e | hv_in
          · have hidx := idx_of_input ib hib_lt v e.symm
            exact ⟨⟨0, by simp⟩, by simp [hinp, hidx]⟩
          · obtain ⟨j, hj⟩ := h4 v hv (Finset.mem_of_mem_erase hv_in)
            exact ⟨j.succ, hj⟩
    · refine ⟨k, S, ?_, hlive, fun y hy => ?_, fun v hv hvS => ?_⟩
      · change k ≤ gs.length + 1; omega
      · rcases List.mem_append.mp (hsub y hy) with hyw | hyz
        · exact hyw
        · have hy_eq : y = z := by simpa using hyz
          exact False.elim (hzS (hy_eq ▸ hy))
      · obtain ⟨j, hj⟩ := h4 v hv hvS
        exact ⟨j.succ, hj⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound_2116
    (hU14 : Impossible true (z2 511) 14 (vars 511).toFinset)
    (hM15 : z23 (z2 511) 15 (vars 1535).toFinset)
    (C : Circuit)
    (hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
    (hsize : C.size ≤ 15)
    (hfun : PEqualNP.MetaComplexity.circuitFun 9 C = edge)
    (hnorm : ∀ i : Fin C.size,
      (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
      (C.gates.get i).inputs.Nodup ∧
      ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1 ∨
       (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2))
    (hS : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
      ({i : Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card = 1 ∧
      ∀ i ∈ ({i : Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)), (C.gates.get i).op = GateOp.or) : False := by
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C = edge := hfun
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply z67
    intro r
    exact (z190 C hmin.1 C.output r).trans ((congrFun hfun' (sample r)).trans (q42 r).symm)
  by_cases hNoNot : ∀ i : Fin C.size, (C.gates.get i).op ≠ GateOp.not
  · have hndW := z212 C hmin hnorm
    have hGate : ∀ i : Fin C.size, (C.gates.get i).inputs.length = 2 ∧
        (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧
        ((C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.or) := by
      intro i
      have hi := hnorm i
      have hfan := hmin.1 _ (C.gates.get_mem i)
      refine ⟨?_, hi.1, ?_⟩
      · rcases hi.2.2 with ⟨hn, _⟩ | ⟨_, h2⟩
        · exact absurd hn (hNoNot i)
        · exact h2
      · rcases hfan.1 with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact absurd h3 (hNoNot i)
    have htarget : graph ∈ execute C.gates inputs := by
      have out := z250 (u := false) (execute C.gates inputs) C.output
      unfold Repr represented at out
      rw [goalEq, z290] at out
      rcases List.mem_map.mp (out.resolve_right (fun hn => hn z132)) with ⟨x, hx, hxq⟩
      rw [z290] at hxq
      exact hxq ▸ hx
    have h467 : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        ({i : Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card = 1 ∧
        ∀ i ∈ ({i : Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)), (C.gates.get i).op = GateOp.or :=
      fun v hv => hS v hv
    obtain ⟨k, S, hk, hlive, hsub, -⟩ := j25 C hmin hfun' hnorm h467 hndW hGate C.gates [] rfl htarget
    have hk15 : k ≤ 15 := le_trans hk hsize
    have hlive' := z63 hlive
    rw [eg511] at hlive hlive'
    have hsub' : ∀ a ∈ S, a ∈ inputs := fun a ha => by simpa [execute] using hsub a ha
    have eqS := z239 hlive' hsub'
    have eqV : vars 511 = vars 1535 := by rw [q19, q176]
    rw [eqV] at eqS
    exact hM15 k hk15 (eqS ▸ hlive)
  · push Not at hNoNot
    obtain ⟨i0, hi0⟩ := hNoNot
    have lt_cnt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
      rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) (C.gates.get i0) (C.gates.get_mem i0)
        simp only [isNot, hi0, Bool.not_true] at eq
        exact Bool.noConfusion eq
    have hc14 : C.gates.countP (fun g => !isNot g) ≤ 14 := by
      change C.gates.length ≤ 15 at hsize
      omega
    have out := z250 (u := true) (execute C.gates inputs) C.output
    unfold Repr represented at out
    rw [goalEq, j96 j30] at out
    have targetIn := out.resolve_right (fun hn => hn z132)
    obtain ⟨k, S, hk, run, sub⟩ := extract C.gates inputs hmin.1 (by simp) z132 targetIn
    rw [j95 q146] at sub
    rw [eg511] at run
    have eqS := z239 run sub
    exact hU14 k (le_trans hk hc14) (eqS ▸ run)
def q67 := z9 [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j76 : Known true q67 := z5 (m:=15) q165 low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def j15 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd15d16630b273,0x11525c6a12412),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe90c286464e7f,0x2c2d009524869),(0x18c06d986cd9c,0x1290662058794),(0x27e6c59e90980,0x2166995b04820),(0x3ebbb2079b000,0xe892284e92c0),(0,0),(0,0),(0,0),(0,0)]
def j16 : List z35 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def j231 : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def j111 : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => z38
def j230 : Nat → Nat → Option (Nat × Nat)
  | 6 => z15 5 15 3 9 1 4 g31h6
  | 5 => z15 1 3 1 9 1 4 g31h5
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => j15[j]?.getD (0,0),j16,j231,j111,j230⟩
set_option maxHeartbeats 0 in
theorem j281 : z24 g31 (z8 q67) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=1) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j244 : block g31 6 0 1=true := by refine (z1 (ar:=5) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j245 : block g31 5 0 2=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j246 : block g31 4 0 1=true := by refine (z1 (ar:=5) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j79 : z28 g31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j246
  · exact j245
  · exact j244
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (z2 31) 7 := z68 (hints:=8449) (by decide +kernel) (z26 (g:=g31) (i:=0) rfl rfl (z6 q67 j76) j281 j79 (by decide +kernel))
def q66 := z9 q67 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j65 : Known true q66 := z5 (m:=31) j76 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (z2 47) 5 := z68 (hints:=8449) (by decide +kernel) (z53 (prior:=z8 q66) (z6 q66 j65) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def q65 := z9 q66 5 [(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j64 : Known true q65 := z5 (m:=47) j65 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (z2 55) 5 := z68 (hints:=257) (by decide +kernel) (z53 (prior:=z8 q65) (z6 q65 j64) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def q64 := z9 q65 5 [(55,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j63 : Known true q64 := z5 (m:=55) j64 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (z2 63) 8 := z68 (hints:=8449) (by decide +kernel) (z53 (prior:=z8 q64) (z6 q64 j63) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def q63 := z9 q64 8 [(63,[]),(95,[101,66,16]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j62 : Known true q63 := z5 (m:=63) j63 low63 (by decide +kernel)
def v66 (i : Nat) : Nat := 0x7213f
def v63 : Packing := (1,0,2,0,0,0,0,v66)
def v65 (i : Nat) : Nat := 0x8000
def v67 (i : Nat) : Nat := 0x17e51
def v64 : Packing := (1,1,2,0,0,0,0,v67)
def q207 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffad506dc8c692839f653,0xf04d190d4828112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9aa3b7e53917e26487f,0xa02a6201004224829),(0x544c503731eb1c38f9c,0x1449d09c60531818514),(0x6d8c223200ec1fc0fc0,0x6bb62f6391ac07c0ac0),(0,0),(0x71d0482cce001fff020,0x70fb0c6f2b181eed020),(0x7fe3c2000ee7f040020,0x7f5fd599feffb040000),(0,0),(0,0)]
def q208 : List z35 := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def j118 : List (List Nat) := [[],[32,83]]
def j21 : Nat → Packing
  | 6 => v63
  | 5 => v64
  | _ => z38
def j117 : Nat → Nat → Option (Nat × Nat)
  | 6 => z15 1 3 1 6 1 1 v65
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => q207[j]?.getD (0,0),q208,j118,j21,j117⟩
set_option maxHeartbeats 0 in
theorem j228 : z24 g111 (z8 q63) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=0) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j152 : block g111 6 0 1=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j153 : block g111 5 0 1=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q280 : z28 g111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j153
  · exact j152
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v35 : Lower true (vars 111) (z2 111) 7 := z68 (hints:=16785665) (by decide +kernel) (z26 (g:=g111) (i:=0) rfl rfl (z6 q63 j62) j228 q280 (by decide +kernel))
def z283 := z9 q63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q236 : Known true z283 := z5 (m:=111) j62 v35 (by decide +kernel)
def v60 (i : Nat) : Nat := 0x163441bf
def v55 : Packing := (1,0,3,0,0,0,0,v60)
def v58 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def v61 (i : Nat) : Nat := 0x420a3fa41fd10
def v56 : Packing := (2,1,3,0,0,3,0,v61)
def v59 (i : Nat) : Nat := 0x18000
def v62 (i : Nat) : Nat := 0xb7d8d20
def v57 : Packing := (1,2,3,0,0,0,0,v62)
def q205 : Array (Bits × Bits) := #[(0x1da64108012bd832f47c,0x1d85960021199906a42c),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac458a9750042f2dc84f,0x4c61e4544061425c84a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9958e417a60021ce0f8f,0x1909e00a3a18e18a0685),(0x67780400a62f50f10f70,0x627201f4c42600710950),(0x52c2796909d080fbf080,0x4042684f5e8240f95000),(0,0),(0x7b3dbae059d52e010080,0x3b3981b0a179ab000080),(0,0)]
def q206 : List z35 := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def j115 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def j18 : Nat → Packing
  | 7 => v55
  | 6 => v56
  | 5 => v57
  | _ => z38
def j114 : Nat → Nat → Option (Nat × Nat)
  | 7 => z15 9 13 2 9 1 4 v58
  | 6 => z15 1 3 1 9 1 4 v59
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => q205[j]?.getD (0,0),q206,j115,j18,j114⟩
set_option maxHeartbeats 0 in
theorem j227 : z24 g189 (z8 z283) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=1) ?_⟩,z14 (d:=2) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j149 : block g189 7 0 1=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j150 : block g189 6 0 2=true := by refine (z1 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j151 : block g189 5 0 1=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q279 : z28 g189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j151
  · exact j150
  · exact j149
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v33 : Lower true (vars 189) (z2 189) 8 := z68 (hints:=536879876) (by decide +kernel) (z26 (g:=g189) (i:=0) rfl rfl (z6 z283 q236) j227 q279 (by decide +kernel))
def z281 := z9 z283 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q234 : Known true z281 := z5 (m:=189) q236 v33 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v34 : Lower true (vars 127) (z2 127) 9 := z68 (hints:=16785665) (by decide +kernel) (z53 (prior:=z8 z281) (z6 z281 q234) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def z282 := z9 z281 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112]),(223,[32,67,117]),(239,[32,83,116]),(247,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q235 : Known true z282 := z5 (m:=127) q234 v34 (by decide +kernel)
def j294 (i : Nat) : Nat := 0x8201ff
def j292 : Packing := (1,0,5,0,0,0,0,j294)
def j293 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def v51 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def v44 : Packing := (12,1,5,0,0,10,0,v51)
def v48 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def v52 (i : Nat) : Nat := (if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)
def v45 : Packing := (113,2,5,0,0,12,0,v52)
def v49 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def v53 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def v46 : Packing := (116,3,5,0,0,11,0,v53)
def v50 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def v54 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def v47 : Packing := (12,4,5,0,0,6,0,v54)
def q203 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda8e80efa31334f8b77110a294fa2c140112476e217263,0x1a8204e622010a10823154424006181028000900212202),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe550613dee46b171e50184200e13000163a237ccc4483f,0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x287218002942c96181045804080031c00109841008504),(0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2428c05eec0a4201a424385293645c4328c32710b10ae0),(0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x38f01e2cfde810414683fb572913092a5d010800038410,0x1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
def q204 : List z35 := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def j113 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def j17 : Nat → Packing
  | 10 => j292
  | 9 => v44
  | 8 => v45
  | 7 => v46
  | 6 => v47
  | _ => z38
def j112 : Nat → Nat → Option (Nat × Nat)
  | 10 => z15 16 41 5 10 4 2 j293
  | 9 => z15 67 277 6 13 7 2 v48
  | 8 => z15 100 251 6 13 7 2 v49
  | 7 => z15 4 19 2 10 4 2 v50
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => q203[j]?.getD (0,0),q204,j113,j17,j112⟩
set_option maxHeartbeats 0 in
theorem j226 : z24 g191 (z8 z282) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=3) ?_⟩,z14 (d:=0) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j46 : block g191 10 0 1=true := by refine (z1 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j145 : block g191 9 0 12=true := by refine (z1 (ar:=8) (rows:=0) (d:=2) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j87 : block g191 8 0 39=true := by refine (@z10 g191 8 0 3 36 (z1 (ar:=7) (rows:=0) (d:=0) ?_) (z1 (ar:=8) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j1 : block g191 8 39 31=true := by refine (z1 (ar:=8) (rows:=0) (d:=3) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j0 : block g191 8 70 43=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j146 : block g191 8 0 113=true := (@z10 g191 8 0 70 43 (@z10 g191 8 0 39 31 j87 j1) j0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j88 : block g191 7 0 49=true := by refine (@z10 g191 7 0 13 36 (z1 (ar:=7) (rows:=0) (d:=2) ?_) (z1 (ar:=8) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j3 : block g191 7 49 36=true := by refine (z1 (ar:=8) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j2 : block g191 7 85 31=true := by refine (z1 (ar:=8) (rows:=0) (d:=3) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j147 : block g191 7 0 116=true := (@z10 g191 7 0 85 31 (@z10 g191 7 0 49 36 j88 j3) j2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j148 : block g191 6 0 12=true := by refine (z1 (ar:=7) (rows:=0) (d:=2) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q278 : z28 g191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j148
  · exact j147
  · exact j146
  · exact j145
  · exact j46
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v32 : Lower true (vars 191) (z2 191) 11 := z68 (hints:=536879361) (by decide +kernel) (z26 (g:=g191) (i:=0) rfl rfl (z6 z282 q235) j226 q278 (by decide +kernel))
def z280 := z9 z282 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q233 : Known true z280 := z5 (m:=191) q235 v32 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v31 : Lower true (vars 251) (z2 251) 8 := z68 (hints:=1358970881) (by decide +kernel) (z53 (prior:=z8 z280) (z6 z280 q233) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def z279 := z9 z280 8 [(251,[]),(254,[32,67,117]),(477,[48,33,133,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q232 : Known true z279 := z5 (m:=251) q233 v31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v30 : Lower true (vars 255) (z2 255) 12 := z68 (hints:=553656577) (by decide +kernel) (z53 (prior:=z8 z279) (z6 z279 q232) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def z278 := z9 z279 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48]),(510,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q231 : Known true z278 := z5 (m:=255) q232 v30 (by decide +kernel)
def j289 (i : Nat) : Nat := 0x1840804ff
def j283 : Packing := (1,0,6,0,0,0,0,j289)
def j286 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def j290 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def j284 : Packing := (6,1,6,0,0,9,0,j290)
def j287 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def j291 (i : Nat) : Nat := 0x2e1d818587821e221614a130f091146478584c0c3c2c10b0a7088561608c040207a04c442860211d1a16112300a10082e1c61311850b0a4746c2c1058458988a3028223838785a5041d141418442a102d2088a0a12225460ac2c10805040f40583c282820b0a1c4c45191c1c4824e230c8c09820a901e8c30705040d0e3618222878514342c181c14442810482548c140e0b08166420584040b0a30885c282a3030203e08a072c1610102428b860a11821e1464106058707110b382838984902d1c1d18284824e230c8c0e201c1670947074642040a0f0b4e183a3022286871d083210102c28c861e0f818409821c149061607c10ac2110440306e0e102e1e00585261c18170708242c1100c140a08406050d0ac1080438303848582821818242f042010c0f840a23821408711c2060407c3c0c10a0f503606183e08206e10587291c1814370b04281108e0d878209840b801412a07050418804020c561f04108080a20504121e003e160821ac3aa6695281e74a5d64a236e2ba1a60b1fbdea9dd5d21bcdaf9a258b17fd7296355a14ad3b92851910bcf88e74d40c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130
def j285 : Packing := (47,2,6,0,0,12,0,j291)
def j288 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def v41 (i : Nat) : Nat := (if i<1 then 0xb102c382e18141e0b0515081b05844813238441e0b28448e13e08641e68382b080b205c2c0a1814320a1f08220f1817080b05100a17058c081a0c8c160a1210200b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe082808592d490e4231f18e446c63231688a8c4ea2230fa871c33216b09e843c15606b0037f63ee9f46f8c7b63d0de34ef1768baa1d10e6871fb8a1c10ddf6dfb6a1afed5f6a4347d9fecd665b327d8fec6861fb0a1822bf15e8aee9710b685a8ac7d5fead655faa354c8a294fba75d35c98e4bba53926e920484a35d15c897437213905c7fc3ee1f14f1476139c1bd0da86b434a1964c846102f39740b4e5902b39540a6051927c934096049023390f883c3e31e60eb072a37e1af0d1c6602fe16a8a8c4d023f10f87fc3be1b60cb05d82be13608f84201be0b604b0190064000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x730608110514260a15041e8407028a0f1182c7c30505c2240382841342a1060e054102240482c411050a0a840b04480b04881e0410241620582440905881e04103c0a0405828a0b05058605040102e0e284c12202828082509942609105c1c202038143058142c0a203c16110511080404828804050447470503c164e18381e3e083c14342010160a203c2c2c204416308810140f211412111844342e1090220f2010160a182416208810140f2010420a1c10081105900821050c160f101c1c0f182416202858160a202c142088284c6070646040703c60a058a0b040e0581450203c14305038407050118a0e2810160a19140a090890120a102c140411864a090882824442a10081c0b028c0a0c0202e0f28441409183c0a0b07101211090c141910470c0e0590162210441e20902c505020142c0a2c1042208290161c1014080e0b918e1a0b8c2304058e8219420281656283c1430785041fa17068a0f05188c060702c9c1038281e4e17040e0aa28101e70805c163040501430284c123e07081dc107828c13088a0c0508e101650ad60140b20281e202114121120281c2e1f041e0a211c162048442430503c404070287040d8441640f04c1e34202c143e081c140f2210080b05101211090f85c18e810140f303c282020641630785040f0a0a8a0f050c1e0)
def v36 : Packing := (136,3,6,0,0,13,0,v41)
def v39 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def v42 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def v37 : Packing := (53,4,6,0,0,9,0,v42)
def v40 (i : Nat) : Nat := 0x834601a000
def v43 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def v38 : Packing := (2,5,6,0,0,3,0,v43)
def q201 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe383f541a14f4a486b2153ac6cc220d9a4c042882144400812c1a03824014a3e21f653,0x3835041a0c802027c003361601060690134460c209508104109022004008a24212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc798b2d38f019ccd955a0208a2083da20800120c010a1d5456e25c86f4208c8c6481f,0x1c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x7f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0x3d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0x80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x8003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0x167c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x147c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x183c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x18382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x119338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x11338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xfc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x6c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]
def q202 : List z35 := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def j110 : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def j14 : Nat → Packing
  | 12 => j283
  | 11 => j284
  | 10 => j285
  | 9 => v36
  | 8 => v37
  | 7 => v38
  | _ => z38
def j109 : Nat → Nat → Option (Nat × Nat)
  | 12 => z15 8 37 4 10 3 3 j286
  | 11 => z15 48 123 4 13 6 3 j287
  | 10 => z15 79 299 8 15 8 3 j288
  | 9 => z15 39 99 5 13 6 3 v39
  | 8 => z15 1 5 1 8 1 3 v40
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => q201[j]?.getD (0,0),q202,j110,j14,j109⟩
set_option maxHeartbeats 0 in
theorem j225 : z24 g383 (z8 z278) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=3) ?_⟩,z14 (d:=1) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j43 : block g383 12 0 1=true := by refine (z1 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j44 : block g383 11 0 6=true := by refine (z1 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j45 : block g383 10 0 47=true := by refine (@z10 g383 10 0 19 28 (@z10 g383 10 0 6 13 (z1 (ar:=8) (rows:=0) (d:=1) ?_) (z1 (ar:=9) (rows:=0) (d:=2) ?_)) (z1 (ar:=10) (rows:=0) (d:=3) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j86 : block g383 9 0 39=true := by refine (@z10 g383 9 0 3 36 (z1 (ar:=8) (rows:=0) (d:=0) ?_) (z1 (ar:=9) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q299 : block g383 9 39 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q298 : block g383 9 75 61=true := by refine (@z10 g383 9 75 44 17 (z1 (ar:=9) (rows:=0) (d:=4) ?_) (z1 (ar:=10) (rows:=0) (d:=3) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j142 : block g383 9 0 136=true := (@z10 g383 9 0 75 61 (@z10 g383 9 0 39 36 j86 q299) q298)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j143 : block g383 8 0 53=true := by refine (@z10 g383 8 0 44 9 (z1 (ar:=8) (rows:=0) (d:=4) ?_) (z1 (ar:=9) (rows:=0) (d:=2) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j144 : block g383 7 0 2=true := by refine (z1 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q277 : z28 g383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j144
  · exact j143
  · exact j142
  · exact j45
  · exact j44
  · exact j43
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v29 : Lower true (vars 383) (z2 383) 13 := z68 (hints:=12901687553) (by decide +kernel) (z26 (g:=g383) (i:=0) rfl rfl (z6 z278 q231) j225 q277 (by decide +kernel))
def z113 := z9 z278 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q230 : Known true z113 := z5 (m:=383) q231 v29 (by decide +kernel)
def j165 (i : Nat) : Nat := 0x201c1814100c0804013ff
def j155 : Packing := (1,0,8,0,0,0,0,j165)
def j160 (i : Nat) : Nat := 0xf7000e77c103400000000000000000b280000000001a4b0b8c000000000000015000008480000000000000000000194112c500000000000000000009001c000000000000000
def j166 (i : Nat) : Nat := 0x3a0f0682c1007018003530883c1a090005830f0883c1a0b0105828128914d00ffd30ffd20ffd10
def j156 : Packing := (3,1,8,0,0,8,0,j166)
def j161 (i : Nat) : Nat := 0x1a0061e14c19d5c5a27598680000000000003207a09d00f06fca2604001a05747a000c02a0632a3a120000109d96845565091300d62b409a8344e000080700011c7a19f03f077c040000000822823e0c5119904c28000f438003db8c0a34a9070001c8a000305800000000000000004850000002c9a000000000117400067e3258001171927a10d1320000000000000000000002dc5501700000000000000002040000000000783f09c0000006b0c6030438102340410100180000e040021000083
def j167 (i : Nat) : Nat := 0xe08a0e48a0841f06c141cc060b42980960f8360b06e021282a8501ca04c2481508c1f040630082d235044910218460c83c1706214904021c1f0680d0a8310d46118304009a2808181f07b04c1b080401d82e0c451583e0d8041886820680c1ec130603b00c520c4341007417661183e0d05c1885020704708c1f0682d0a830090412090390960d82a1083e0305c148dac1a04b08c1a0482d14432094832092338460e834170521904a81804810c1f064210c82e0a45d40b01d8360383e188402a04a411c2307c190c04009380583e0d82e0980e0007a307c1b05c050a038c01e0f83608076010621a801308c181082e0c450f8460d8241706228601203c1f06c00108310d40278460f8341706214704b08c1f060400b4320a460f8360a8460204980e04b07c1b054230182a0b4e1183e0c86012504410c2307c1a0b8290c02520581b83e0d82e0980e0007a679e5fa4562da186081edddd9be5ab993d7715f54512ad131004eb0dacc58b2ca288d47a86545503d42f817c003ffb02987ff46530ffea9a41ffd81483ffa62907ffa2520ffec4a41ffe39483ffa72907ff86520ffe8ca41ffd83443ffb04887ff54910ffe99221ffd39443ffa52887ef92530bff0ca61ff930482ffd12905ff62520bff1ca417fe19483ff240885ff8e510bfe9ca217fe29442ffa52885ef92530
def j157 : Packing := (30,2,8,0,0,12,0,j167)
def j162 (i : Nat) : Nat := (if i<1 then 0xc0699c07a0000f6a00000d0a00000d0a41a7310817080100800008266d0af00007b6d0030008ec08b0000741e0000303297bc87424243b0c7624c10564a700000749a04439091e0a73065106d165400000000ca280000067630ae14350000124a4006a062000000000000247e548200000000791b20cd0000a49d05560256000000004319348e596ed611e010f06bf6de361e27dd40c0e26d50abf0128094d09bd334e48a0000fbc580ac7bccc06af4a8a0724abc8767931b208a000020401087b070641a00000000c7a1c0b4e0a10038c49f103714a027a6a42bc2c5444070a2aaad573e8732d6b80000736eb07400008b703aa8e4d2f0930000c082c743200a0096c495006c55976020000000000000c2bd109d000043a70000e47bd061304ec09555c1405580cf84761492c03ba537405220681092b10f6076040460a80b73000000000000000080ce00002562000000004568000080d1648c00000000d0390000000085ae00000000c01e00000000bb742033e02c40010000000085050000c0d400007a43a08c204ab7a8e24dc2bf000062bb0000b2ba17250000f4d9e0980000b059b428504100000000875b000060bf7496904bc84330169197305f0000f01bc254b01a07d0641d000030d9c13f103d668d009e70512466e42aa05034adeac950b782a7824b67afc0b884a376d4624223def0900b6f2b1cc026c045c0bbb73ad0c352b940db1a55a04480d0db5540753262b05b503ca0ccb0d8109cc5bd60d23a1c113ad0d500000000721a3035b00d5088b0b6d2b3802b509a1029b02d10baf02ec04f3071b0df30244049641820da505d04d4f134726720adf06000006054f0dc28550000323fb9cd0000f04ca0c6608f502af0a3a63ec403a003c775c04210369077c105307e40de126fd391903460c98069c49c0000c956e0470000a1b9000060230000608380beb00fa07f87d5e464d085000020bcf0c2503a0354e4a20099e05a0002301c10c56073124607cf50dd41324019eaca503e836aa4d3554d259890b362375004846500000000dbc90000a60be1a5000044a7006f000000000000000000000000447800000000e0d300000000609f000020138053d0d7000000000000000042ae0000000000000000305826a94a2a90572043b42ff6448078f07bc1981bde525f9097308400001044020080502c0000c0200806000310181000c0800c020040000800008001341803c020c0040000e0000000400024000185103802060050000400c000741d000020240900c0505001060070040800c00148000400b01804060010180302c09070020001e0080a01c060340001000030040081f0040e0080101415000010080200405020020180c01002004010040101008008170000001c1f018090080600c060140308400040000181e0040400015 else 0xd00e0205c046877d908d000010c8e02500003154f0a9507c41b837d680b50000e0aa8028e63a4bb8b07dd06692a8549145291079000000000000b0b2f05ee6690199a0d6e2aa547a30a6d04df0483009100011de0000d85473b8200c0000c0e0eb549022e260e13e0015000002491018b74c3499142df12942bc00bd5064a0cb2786e089800bd03f7bcb50310000e027202f601dc005e2680a67000090a58014000040ca89667007000000007086476600b1cbca3480000010c160b09021848bd01ff06eb0b9f011aa4c02c18017c0c473d23067763200009063e05)
def j168 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffd9a4c910fff61539443ffd824e510fff54939443ffe8a4e510fff61529443ffd834a510fff54d29442ffe9a60530fef606494c37fd5286530dff625194c37fd5946530dff4a5194c2ffe8a46530bff629194c2ffe5a46530bff8a9194c3ffa0a46530bffa6953483efe6a60520bff8e9814837ff9a60520bffa69814837fd9a60520bffa6931483ff9814c120ffe54530483ff98a4c120ffe56930483ff91a4c120ffe4c289482ffd3aa2520dff54e894837fd31a2520dff4ea89483bfd8162520ffe4c189482ffe3a62520bff86989483ffa0a62520dff4c5894837fe1a62520dff46989483fed528e520dff62639482ffd8a8e520bff56a394837fd818e520dff546394837fd8a8e520dff56a39483fed524e520ff74c5394837fe894e520dff625394837fe594e520dff56539482ffe8a4e520bff96939482ffd5a4e520fef92939482ffe1a4e520ffd60619483ff93086520dff626194837fd3986520bff62a19482ffd3a86520dff54e194837fd8a86520dff4ea19483ff93046520dff625194837fd3946520bff62919482ffd3a46520bffa6983442ffe5a60910bff8e9824437ff9a60910bffa69824437fd9a60910ffb60952443dfe7a54910bff8e9524437ff9a54910bffa69524437fd9a54910bffa6932443ff98548110ffe60d20443ff95348110ffe62920443ff95a48110ffe4e9204437fd858e510dff60a394437fd528e510ffd54539443ff9204e510dff62539442ffe8a4e510bff62939442ffe5a4e510fef92939442ffe2a4e510ffe829394437fd854e510dff609394437fd524e510dffa29394437fd8a4e510dff969394437fd5a4e510dff8a9394437fd2a4e510dff616294437fd838a510dff54e29443ff5514a510dff625294437fd594a510dff4e529442ffd8a4a510bff56929442ffd3a4a510dff60d294437fd534a510dff629294437fd3a4a510def606494c37bd1a925309ff62a194c27fd5a865309ff4aa194c37be4946530bfe829194c27fc9a54d20bbf9a9814827fc9a4c520ff654d30483fe9524c120ff64c530483fba4a4c120bfe86930482efd6aa2520dfe4c2894836fd6aa25209ff4ea894827fd1aa2520bfe829894837f930625209ff869894837fa0a62520ff64c2394827fd8a8e5209ff96a394827fd5a8e5209ff46a39482fbe4a4e520dfd606194827fe8a865209ff62a194827fe3a865209ff4ea194827fe9a60910b7f9e952443fe95248110ffc54520443ff21a48110dfe482394427fd8a8e5109ff56a394427fd2a8e510bef92939442ffa0a4e510dfe481394427fe8a4e5109ff629394427fe5a4e510def929394427fe2a4e510dfe829394427fd8a8a5109ff56a294427fd3a8a510bfd869294427fe8a4a5109ff629294427fe3a4a5109ff4e9294437f61a4a5109bf5aa894827be4a4e510 else 0x1150584e072118a1341000e0200a01c813383e00d80d8a60c0200be86a016b2309942008040026705810583007e0180f06010081435583185714e4692e868103813e0dc1380039e298302500e4812e11c189160bc18c5024a18382d0821201750a05e04d004c1260cc160ba851820807611c8c1bd0a02670720841501300fc1b0660b08f42940a80360ac160e42320908a8083c238392321982f05044470723302c0860a086c8c1fa38470702cc1a05a0a06604286026520a041c500983f04c040e10a847230200a004981f03da11c3017009304100e02786040a1a0ccfc1c19b0c013434081b83f06e0bc0407009370106c054108092a0b068040070266198281c03f483e07bc33026030794358a228430705a0a80082e03382f0502804cb03a01f01f05c140ee86c096469e0dc1705025075c078a03906a03954200f807e0d82f05038812c3120381b8210240541b035068805a0928602e0125e11c1c04d0c066503e01c19d0c050024dc2383833040024a0a8193140634301802f020805c04016e0404982c16314a180995c1814e0a61b43015810382a02008414d0cc17828140264813a19c50138260206e11c1b05e0c0445e0fc1b82f01c14038d05ea09440cb810900c9ffb3fba7f54fe69fc53f647e24fc09f583ea07cc8f875eeb3d8f7abcf4b5e733caa78c6f0c9dfb3ba476baec59d67ba9e74dae8c5cefb9ae72fae531c8db8df70eee095bef37976ea0dbcdb50b65a6c10d705ac2b54969eed319a4ab44e6866cf859d2b3536602ca9192eb2216388c59d895b0ef6166c185812aff45f5abd997952f045d7aba05722ade85b2cb595694acd75920b0f9606abc65714acb55682a73546ea7ed4da29835262a3a9451a8674fd29eb53b8a7404e1e9b4d346263a4c289659291a4fd499891e920ea3cb46f28cf518622ba451288850e2215c4240830d038a01f3fc67e44fa51ef83d8e79a8f069dbb3afe74e0e7e1c8938846f3cdbe9b4135c86a48d2019e3332264fcc7118b130ea6110c0417b62ef45ca0b5a962c2bf656d0aa614ef29505184a0793a726aa4c38958925423d8461089390f62132411c7fa8f8d1e603ba47510e3a1bd036b06ad0cfd195630e05f30b7e16422b1053e8a2b1370256c47f08a1105c1f703ca874e0df81ad433706320b9415b4277848708280eb01a7831305ae0a4012a01f7030804c80650083008e0003ffd5260530fff669814c3ffd5246530fffa6953483ffd9a54d20fff26953483ffd5360520fff4e981483ffd9a60520fff66931483ffd53a2520fff54d89483ffd3162520fff60539483ffd514e520fffa2939483ffd5386520fff54d19483ffd9a60d10fff54d82443ffe5a60910fff56982443ffe3a60910fff4e982443ffe9a60910fff66982443ffd8354910fff4e952443ffd9a54910fff6153244) else (if i<3 then 0x4f8387aa10c299184938070260f816103c8060f00801614330180aa03a8681d0ea70920603b80e0200b0d03b830460414358a010386d6294342d10120660b60740804e37076474340e8752f040920f301839a1b8318a218306501e1980ee05a1a169009021061019c1e8681d0ea8e0e0603500e0b4503003d820390925e11c1802073628124c80c1c820058460e0802b82c02204c1c9c910340740e41006831070ec0681c820058608c0381c8130ea5c06c189102e0be04c1c824a14c37062c1602060e04c1c949100804004c1c94090150201a08c1c3a0100724244c340a8100d05a0815d8a01d0e60b0c0683080b0421a80804e381642409860941e06a01e04a82e0408d45305b235d070341a8396030e00ce8660a61aa0e2040138c2f00e47409894142b603021828388273919c080443802cc16c5291a03786ee11c1f05e0a2c470d404b83e0361b8288c9c1ed0c0da0b036148e05e06609880401ed0c0661b41606c38570bc040131019a2201d02d8306b04d43305260922201c0400eb0da1982901551101360c1a819e0a61b43130140d0100d20e4a888080110c41570502c0b484440380581802a040341c31067a100a412b238127035c198640907050be18b83833a10c32049c1100f0aa0581d03934220680382f03a020098f4358a01604c4e020968405e05c46583c09450860e1603081c02d02413228405702203d91c3a0727e0e0380b03a04c5a101981a30c812124c0d807016074098a0cc2f86281c0a70202562982d91ab8301ac16c3305038340e0420f83101d0ca0cf0550d618a07982f0203702ac501c1c0750d628168321782e030cac1812d0d0b40990c180750d0660f82d0643d0d069c198284d092148ec140800ea1a0843182804c80be08583824a0ac8e049c3003360e0918450c812705c17d1102461141591c0940110740401c901085e62804013158301006609888882f30d020098a06807858014178080263862238c8c1982628570c202c1085e020098f04810860c080900e810a18c5186a819a2205c0842fd0503a0900860a61ac8d8c501381004c44440e81085e020098cc8b8370581703583f0181ec2921740d818e0dc041c30a01e80b80f78650a05e038c01d91f0ca14100071b83829072c328503501c703616c0c03ae034282d04d01e906e1641080e02a1341a1c08058041c0009824310ae11c188a60b2af83024a01b0410adc1b0650a026085043426813048c180760c07213d20602af1481c8641cb23a1a1512434080210738300730a09e809b8301c80f27070220e58560c092150072096f08e0c08009914020704a83808514c18c34289f8470605c0808a0530200bc09a5840060200bb0660b0a54511c238360bc194500818098464160b01c845320303541c1ce0c0a2c342804f482c0480e683e0bc18c28e else 0x602a00c0607219233089071224a0e06c1703c009108488f8348c8211060cc0c40e02a803e2000982403a20cc04c1201901c07c418173b000260903505f2d0084448817049284908490849082ea2804c741c1701f08c04c3301d382c0b0481c488230100921dce0e430381f50d08c1a8a0b031055a0804c1c9a8201f0420cc0801d30360b80381121223660ab41417025250760c0f00d12829190ccc8c3806d3057a0ac203901a2d05610470108460da64161a840810206a1040880d0102d0183246419c12238090e20419d0c0424644018400100224640a83330100420cc230240cc60fc03808021206681c1aa1d120740b0421a808160711902c16c1081002a781c4721d06a24110200cc3512090210201a88040108330d440c38342f0390705e0ac883ff06e02c1c1430a81e90be18b83b06a14c32071c1d00e03741014026307e01c0e99183907060fc0381d30c0720e0d835838370681f68540e0708c1a15c308090bc0e41c1f0681c020c8e07039360d0681568530c81c0e0e0482f03403a0381c18177070d405416140487305c55c249435013e0d80d86e0c2447a144881707c21070ae1cc16102c50a0201c82482f3073058260f03808039c18c2a869c23039c0b4342d160580e0300700f02804c70481543500e0301681c1e0581e0680480c02801c0991c190760ca28c34081b83020a28c340814248240f581408514c160b9004c2c7060681cd845140928a280201801005c560801c098490725034c228a01f0b4505c0680eb08c19450161c3b01a6080e4249409d1403e1689c181a603c1945016198201003d41c1603930100dac283402e2a050400b0700d2a81c0f208016180d05562808016143c87b03208016152a813079420398576141250))
def j158 : Packing := (225,3,8,0,0,15,0,j168)
def j163 (i : Nat) : Nat := (if i<1 then 0x162c394547813402c00000508ea82ac1a81b473db348b2ec0000c13000005a2b8c133e13ab65580001c1ae00004007902740206612700004301c0266000080b495c60407a00000000005feca344502000000000000168c1560204c698343a0e5d090c1e809126000060ab04e680001a0f8d073005c4402000003720a01fa80e060e2b0cfc839d024400000000602f6823fe89fe06c05d5cc06140ba90c09a17009fe0000b2a6193d351e60000e00fb021052caec382039b00a7003ac0525407b0469c1455747000075d15c0c8019a201912aa442af61a5804990594c151a5a7000000001e0800120303b801c5c0060000000000003413c685e60bf485b66dce017d50b78000341f73748f464c90ffc1f8a45d9053811dbc33c000000000000000018002000000000009944cfaba57935400000000607480002c2f765325083ddd2442a80000518a5841a888ea015f2a10000000000000c05ae52a9c0aa005d000040352661561632085781ed1ebe4040c0d40951d93356075000048053826e8efa00005867400000000000000003116e698100005de8000ca40d3c09b20588667b098690a4a002481e940e800002015c00000000a040002fa429cef3d00007919e0323600e00000000242a4000080ae7a2fa184c610b0000782c680a800000000381f41df0111850c100000d2e7a046d0cc126494f460000000040578000060630000410f40001c8f9a08050098000000000000703fb8136000050768000000000000407c80000000000000000000000000a04b0000438f682a1e15510d1d010e8050959000007020e6eaba0f7500d206380000809100003346102f321732423002ce00cfc44b00243030e42906714a052580ba4246000087831181a087cf4d49155985990278000077c8a80fc19860000b00bb82a942ee0000c0810000000000000d05000000c34c00008092c11980001819500000000000000000e02200000000000000000000009e7616920000000000001a0960000283fc0000c07400000000083180000000000000080000202c06000130080100001024000240300c0000400010000000000c0102c110000200c010000000401000040180b01801008000040100806000010100100402000020180302c050000101801008000000700809030000140c00400000020100200c0901c060080e00002010020000b0000201400020020140301000028040040a0040500808028030040004405008000000000001084030200100c040240100001000040000a034000080a0040000406000010040001c01004050440200003004030740200002020040180204005000000000000407000000000200c0601c090000001c0000002000000200401001000020080000001038000040a00c030040801000000000040004002004090000001401 else (if i<2 then 0x5c5269c00000000e01df022c02c265a8044318602c0f0005cf023d85d212e3414740ca301a79b4a000000004062c00004031d408c0014c9f161316000b0625d121371b00c38000000006128000000000c06c6987000c00002554be1750000183b80138000060a5e3e2f00a6000000003c46b51ed811240ae80000814c00610000504b400000000e3238000001f4000000000000281a20000507a800000001a4066066000039723e0240000385d8687a0000c47a0000141de0000000000003421c0000b02f9006f002200000000084580000e600801a53102023c0000000000003016dd00d000000003c34800000a52c013c00000000c028981144558006ab06580003526cc206102d4061400000000100380000000000000000000000001e0f100001002000000000908600000028a205e820ec2c59c15a606660a3381b000000000aba6552ac426520c2aa9e00002c72242c51075fa185c015c09464579dd1a00ece168d430480dc802d65910024f8672c4eb608f44b968214073f61097070781e4000060dc000040567009c0000f0cb8000000000000206f60237e190a186a0ccd88e4000000001b23f02080001e0210000502dc00000000703f80001c231c16bd1be00001c14a68b290b900002421a0000e04b80000000021530000000020125a5aa402800001434ea0fd9037800000000000050962263c00018590729e000015b3e0000682380001818301240000204f40001e03e00006037e028500bb7a7980000000000000000580ea424c00000009800000000000000003a64e42d900d080a243bc400004101f0be00001ae9b60dd409c300940165a03cf09a5a29c000123a50000705aa810e000000003826302dc0000000000003901b685bc62380000000000007016382324ab5f75600d000001c1908533fb3a000000000e8d000000836c018fc0cda01c99417805be44f40571043c0000000000007309c01120000a0c27031bc1ab20ea00003033b13048027508dc84a641e15316545c8000340da0000200cb038d52c40000605c886280001218300000844000000000d04479c600001453d50035a62f401b402af0c9683daeeb0e06004bc6854490b08086e0358000183520000d0c68000190bfb537984180003c0e400000000000000001055620604a57912c80000b025000000001612f00002008c00002033000000000000000000000501e881c9e13900005c984c11428d7000000000d19400000000202a710bae167720c784d69db9cebd10c7a1b9c8d9264561069284fd01954012a0b20000092dc8105eb39e831000016062c0a780000000048c30000000000001666a0000584f990280000000000000000074ca705601e44413400006763b02fd40d1886290b82215c42220000b0c423be48226000000000000241d8000046643016c else 0x20505932c000090bc6027f822fc020f09d9066e88c02518c59c0000202080000757a2c045df1b205900afa065800004114049d404af416802a489a7794b24019406e1152e11089e78000000000000000000000802093b1800000000000062641025d087f405e72e3cc3547594ea49705280344000000000828c0001408180ac000000001c8bdf02c2850c00000000d0c80000000000000802150314000000009bd180002003984ef6058000010a88e884a0709033c81420000e4bd800000000801e0000604579996000040c98000000000000098e8000000000000206c800000000802fb265621e00001e08eb0648000181e6000000004815901e5c140c4418000000000000000008240004400000000000000000e108000000003c2b400000000581f00000e8a38230c80d4d11646650000705e80000815b30020000041ac0000501c1cd67815f2095b983e802e4057a11cf2a5000018233af9af0a61836a4254e14de))
def j169 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x56a394833bea8ab51ca411ffa2d5a8e520cbfcf6ad4729047fe1b56a394823fec5a351ca411ff56d1a8e520adfad744a729063fd89a29394837b6a94b49ca413fe82d5a4e520df5aa5252729067be89929394833dec4c949ca419ef9664a4e520cf7ab3252729057f69b606194839fac0b130ca415ef92d3986520edecd6c0c329047fd3ba2a194839fac0b150ca411ff8ed8a86520cfeb031d4329047fd8b8ea194823feadc750ca415ef92d3a86520cfeb029d4329047fe8b4ea194823ff2da750ca411ff56d3a86520cf7c969d4329057be4b4e51948277f35b148ca413fe82d8a465209fdc569d232904ff90ba69834423fecdd34c1a211ff66e5a609108ffb371d3048853fd8be6982442bf695f34c12213fd46e9a609109ff2174d3048847fd9ba69824423feadd34c12215fb8ad9a60910cbff373d2a48865fd9b9e9524423fecdc74a922197f9eb9a54910afda57cd2a4884ff90ba69524432ff3d334a92213fd46e9a4c9109ff2174d2648847fd9ba6932443fb4a9aa490221f7a9ed5248110bfd456c5240885ff21b62920443fb8a8ab49022177e9ed5a48110bfe436ad240885fba4b4e920442ff90da7490221ff854a1a48110bfe2b70d2408855fe7b54a39443bf4a92411ca211ff96d8a8e5108ffc56c54728847fd8b56a394423fec5a551ca211ff56d2a8e5109ff416c5272886f7551969394437daa8c949ca21bee4824a4e510cf7b1325272886fe9208a9394437dd254149ca21bfc5460a4e510abfcf6a92728877e952481394423feadd149ca211ff4ae8a4e510adfcd6c52728857de3b62939442bfb0db149ca215fe82d8a4e510cf7c96c52728847fe2b629394433fd05b149ca211ffa2e5a4e5108ffb172d2728847fd2b96939442bfb0dab49ca215fe82d5a4e510ef7241252728867be8a929394433dec54949ca219ef96a4a4e510cf7ab5252728867bd85929394433dec14949ca219ef54a4a4e510efd241152728867be4a8a9394433f6a94549ca211ffa2e2a4e5108ffb17152728847fe5b8a9394423feadc549ca219ef9292a4e510afec36952728877ba4a8293944337f35b1514a211ff96d8a8a5108ffc76c54528847fd8b56a294423ff45a7514a211ff62d3a8a5108ffcb69d4528847fd5b4ea29442b7f35b1294a215ef92d394a5109fec36c5252884ffa0b629294426ff3dab494a213fe82d5a4a5109fec369d2528867f589869294427faadc3494a211ff4ee8a4a510adfcd6c52528857f61b62929442bfd05b1494a219bf9ad8a4a5108ffc76c52528867f61b629294433fd05b1494a211ff62e3a4a5108ffab71d2528857be4b4e929442bf715a7494a215fd86d3a4a5108ffcb69d2528847fd5b4e9294433df25a7494a219fd86d3a4a510cfeb150d2528856be6b606494c3fa4a9aa498241fd85495148110 else (if i<2 then 0x21dfb609528e510affd16a94728875fe7b54a39443bfcc2a411ca219ff5498a8e510cffb04ad4728867fd854aa394427fe55b049ca2177f9ed524e510dfeaa345272886ff920a29394427feadd149ca213ff4ae8a4e5109ffd172d272886fbe8a929394437dec2c949ca21bef60a4a4e510df7aa525272886fed528a9394427ff45c549ca213ff96e2a4e510dff51505272886ff98582939442bff15b0a9ca215ff2ad854e510efdb04a92728857fe8b54939442bfec5aa49ca21d7f9ed524e510aff956a92728877f985481394433fea95149ca219ff5498a4e510cffd152d2728857fe8b969394433fec14b49ca21def6164a4e510ef7aa5252728877ed528a9394433ff2d4549ca215ff96e2a4e510cffb0b152728877f98582939442bff1db0b14a215ff96d838a510eefb0aa9c528877dd8354e29442bff45aa714a219ff60d5a8a510cffb0a9d4528857fe3b62529442bff45a7294a213ff8ed8a4a5109ffc76ad252884ffe8b4e9294437fac2c3494a21bfd60e1a4a510dfeaa70d2528857fe5b60d29443beec1aa694a215ffa2d534a510affb16a9a528867fd858e929442bff45a7494a219ff6153a4a510efeb070d2528877f553869294427fc85d34c0a615efa6d8192530ed7cd6c0c929857beab606494c33dec523524a619ef4a91a92530af7d168d4929857bd8b46a494c2bdf2da3524a615ef8ad1a92530abfcf6a94329847fe5b62a194c23ff15b150ca611ffa2d5a865308ffc56ad4329847fe8b4aa194c23ff2da550ca611ff56d2a86530cf7c93452329867be49629194c277f35b148ca613fe82d8a46530cf7c932d2329867be498a9194c3bdd24c148ca613fe62e0a465309ff2174d2a69066ff9b9a98148337ecdcd4c0a411ff66e3a60520cdfcd5cd3029053fd8be6981482bfa8df34c0a413fe42e9a60520cdfcd4cd3029057f61b669814827f695d3498a413fe42e9a4c5208ffab64d262905efa6b60530482bfc4daa298241ff4605314c120bfb476c5260905fea2b62930482ff515ab498241fe654e4a4c120ff52a525260907f9931929304837f4a943498241bee9291a4c120bfd4568d260906ef9305aa89483beca9a6144a41dfa54930a2520efb262985129077ba4b4c289483b7c982d544a419bf54d6aa2520cdfad49d5129067dd314ea894823ff2da7544a411ff56d3aa25208ffc369d5129047fd3b46a894837ec98474c4a41bfa8aa0a62520dfd2a505312906bf981829894827fc8dc14c4a41cfe6053062520efb262983129077ba4b4c1894839fac0c34c4a411ff8ee1a625208ffa770d3129056fe6b469894839fcc0c14c4a41dfa8aa0a62520ff92a498472907f9a4b4c239483bec983131ca41bf64c15a8e520adfcd6c0c729063fd8162a394823ff2db151ca411ff86d8a8e5208ffb172d4729055fe7b else 0xa8f29eaa6c2976a4f2902a32285ea0927ba9e027169b726a298825b695f254293c249e91923e28de230e8b5229a892220e869216a84620c682320528001fae7dd1f3a7c01eae7911e0a7741d967571cf27281c667051bda6e21b4e6b91aaa69c1a1e67919aa6501906633187a61017d65e7174a5c4165e58315d2566154654314ba51a13fe4f1138a4d413164b7128a48e11e646b112a43c109e40d0fca3d80f263bb0e823920dde35d0d223340c963170c0a2f40b962cb0af22a20a1e27309922560906233089221608061ed077a1d007061b306921900606173059215604ee12d047a11004060e103320b802a607100e20005fde3b669814c3f5f35b0324a61def66d8192530ef7aa4c0c929877bdab606494c3bdea923524a615ffa2d5286530ebfcf6a94329867fd5262a194c33ff15ab50ca6177f9ed5246530ef7aa524a32986fed528a9194c27ff2dc548ca619ffe6a9a54d209ffb174d2a6905ffa0b669534833fecd134a9a417bf5ac9a54d20ddfaa735302906efd3b9a98148377ecdcd4c0a413ff56e3a60520ffb136a9a60907fd95360530483ff4a930298241fbe9ad814c120bff4b6c0a60907ff18154530483fdcc0c94982413ffaad53a2520ffb2a698512907fe9524c289483fdd25a6144a41bbf54d6aa2520ddfc76b5512906fed524ea894827ff2da7544a413ff56d3aa2520affcb698d129077f9514c2894833fea8a7544a419ff54d1aa25209ff956a9b12904ffe5b8e989482bfeada62c4a419ff54e1a62520affcb6c4c72904ffe5b62a394827ff45ab51ca415ff96d818e520affd16a8c729067fd5162a39482bff45ab51ca419ff6055a8e520bdfcd6c0a729077ed52a2539482bfeadd129ca41bfb54a8a4e520cffcb3452729067fd59a29394827feadd149ca419ffa265a4e5209ffd172d2729067fe89569394827ff45ab49ca41defa264a4e520df7d1525272906fbd8192939483ff8c0a610ca41dfd6053986520affd169cc32906ff5814ea194827ff45a750ca415ffa2d5386520efeaa6c0c329077f5814ea19482bff45a750ca415ffa2d39465209ffd169d232905fde3b669834427fe55aa6c12213ff4ee5a60910bbfcf6ad304884ffe5b8e9824427feadc74c12217ef52e9a60910bfea374d304884ffd3ba6982442ff715b34c12217fd86d9a60910bff416cd304887f6d5360952443fb72db04a9221f7b60a7a54910dbfb073d2a4886dfd3b9e9524437f6c1474a92213ff62e3a54910dbfcf49d2a4885fee2b4e952442bff4da74a92213ff4ee9a54910dbfcf4cd2a4885ffa0b669524427fec5d34992217fd86d9a4c910fef30aa9a40887fd98354d20442ffd45aa690221ffa60d5248110ffe306a8a40885ffa8b56920442ffd45a7490221ffc6161a48110ffe3070d240887ff15386920442bff15b0b1ca)) else (if i<4 then 0xd8428807c27a82460000ca136320909b101d84288084234401e0b011c302a00205a089202a8428826c214405811c201008c102a80904084d9010827426c6066118201806b08e18080460804c0b026c60261182d0809cc0909b2019842880f0224413404e122309a0931012842881040040ec214882411a2033086103081d0430c024238501c01202c118408308e10318048458c048234581c0de0bfc15a1a10a132700502c08e181e0448822c2145a1a0b41123b07049100001f0248c0000f8124762800406410c4083085170201f0810022c40ca126208b08e102f8198248c17f4341246e0a03a116303e08b100483f80e84c0431407422c412e0b41123083723e0a096238602482d0449025782a039c30810611c209408b101e00eb9184290094214405a0000e6126404100104008b202f81c0430c2481682246042112202a08b10000190430c0f024440e4122202d000032086201f048080b40000c8218808200207610a406008f0861c08047081ac238410002011a301008d1037846880cc234410002011a306d7140391819846081c8224502010a2010086103500808c5007421460c010a2b140861008024880f8214408200207610a406b085100802d08040140403a116204102a08a05a089280102d0448c0f80841406e2810c2c0bc0d31430af06f05f01c0f3574a8699181c80981220710c844842a4c8c04e8282200cc06421c2182153bdb6f1bba66e2fb716d5bb486ccfb1f6c5bafc6b87acd6b13ab66a9fa9f6a2ba7c69b7a656973a4e68ffa3168a3a14682f9fd67a39d467179b766bb9a0665f98f661b97865bf961654b94464a791564038f2638f8d563338be62d78a7627b88461bf861614b84a6107833609381c604f7f95fab7e25f677c55edb7a25e6778b5e0b7745d977575d3b7465cf77355c6b70c5bdf6e95b6b6cc5af76af5a9b6985a3f68d5a2b67c59b7659594364258b761f585b60857ff5f757a35e057475c356eb5b856d75ad56935a2567f597563b58655f757555cb564555754754fb52a5487519542b50253e74f1538b4d452ff4b152a34a0525f48f51d346c515f44950d3420505f40f50033da4f473c94eeb3a64e2f3774dbb3664d5f34f4d1b3384cbf3274c6330a4bef2ed4b932d64b372c54af32b44aaf29d4a5328649df2694983252492724148cb22447c71e347231ae467f18b45f316e453713f44ab11c441f0ed437b0c442d70a1423307e41bf061414b04440bf021404affe3fbefe13f4afbe3ebef9b3e1af723d8ef3d3c8af143c16ef73ba2eda3b16eb13a8ae8e39fee6b3972e4838e6e2b3872e0237b6dd93712db6366ed8d35fad6a356ed4d34fad2a346ed0733e2cea3326cb5329ac9231f6c6f3182c5230c6c233052c062fdebe92f52bc62ec6b9d2df2b622d06b2d2c7ab0a2bd6adb2b1aab82a76 else (if i<5 then 0xc2146102406a0bd0bc200d0350828821441704013077180803b880d01241a86146101e0101051840900f8562807c206307710518422c2116106a0831807035048901a804840da08a176306a012103782f081ac0584020034201206a100b040401b44174100029826c41720de20b80b706f182b841a8048436c16a0be3080003105a840481a84136109b080903508180203201c20180551023040009b0823040002c084d040f82136109b08019c0a040660ca205f0291045870380b30e86078102508355838822c2116108b083501d080e8058402c07402a301601510458422c207c1006084584a83005a1022c203416807c3065067103802f05a0c1781880b061161062081f01e0a0b60a817817c1b42acc116108b080e832881fc22c1806e0a12411602a40b400501518458422c20be0522006084d040f007040421033080b0090818007040be0522018b071045840481a84136108b08030401c200c103c01c1019840401a840480be205f02910458425419c400e10060907044881682245e0de0be03854f6781781a6ae808e089100d81d047044900600e82c822c8130116200908e08918130458814822c40bfa1410a13381c503c0a9104b03a8588c1942bc412c16015e302dd0a02f0a3201c851881040040ec214807c116200905a0891f0682d0448d0380e0403a116209408b1006845881c8224400004a11c30930861043049881a824c214606410c201009310080498800007c21860e6126250a02e086180000e8458c1b410822c6136152230ac0e072049e0cd0d30390198070459012422440ec11c202508e104184708094238403101e11c303902508b181c8428806007422c610611c209302008b18170448811a82c0b8604a116202508b10500458a16380f83024c802012614630ae01008918458568518c0b82a4405ae14126146408b089101284708198068214603410a204908c100d042880b007824c604a11c200d02508e1824849880b0224405400407c07210a506701d085180d049881980680b0603e02611c301308e10098470826c2385a100e60ce15811a5010093101e044880b0224407c126201f0ab100203284d8c19426c400207610a306302c09b1835016855017842941041b81402a4802615004014e116501d04602c18530428800020021460c203a10a306b7140390a2200980e8428c074288414a02e03a10a4012086102b82481c8c04c240462810c20720a4100f043081c822440ca00e07c10c403e085102080081d8429004c24040ca03803c09a403e0a31020045881040a8228168224a07c004144120406b085102484288000074124610002010a321208d1016815050839849940b40001cc24c805a0000e612640100a01008048082008e8218602011a202d000073093200e84f8826804024060e8080136306f085104 else 0x910e079ab8048cc8822c246c28318b342b14632644405db0a0a5322241500c02e84e9007803c418a0c405830be05f0621857840b38341bf038810203011602a40830b401518458420020c40340d420b508350620618c04c090405c092208608430426817c402603a2025039101c841241a81c86048102e025101280d83b8c1b41ab41c602603a201d0131051040b804c418410130851841ab41c41161049033102f83d0809017c425a03e02603a402401f083182481c8530c09017c40c003e203c080104d840f015c4136103e03c104d8610430415c1cc981c18009230a6071103305f880f02146103e0be10355838828)))
def j159 : Packing := (427,4,8,0,0,14,0,j169)
def j164 (i : Nat) : Nat := 0x2d31e04e409441e80000001c06f00380000000000100c3816e56a0003010a1b2a03200030208026f04420ab5cf80000001a0e280ae8350000e00c000000000000002c17223600000000917ca39f06306f581e0000144aa0270140000b08884c5c46301e70000003cc30000000080bfccd800000004d0380fb014307e6049819800e071b40d3116623380100003c07b830d65a0000821083b3015c10e8015dbd4046a0b7c590000606d68b6c1c8000000000000000000000080700000000792e000000000000000005c0000000d080000100353b000010010000281d0001803349ac0010000000000000000000000000000004023e26ec058000202707030100000b41c80f941950377049a0a501d730c005600020068dc0b02000000006a21f18640b180d68c0d00a000000000000600000007010c060226000107010100000001000004000001040100020300050803
def j252 (i : Nat) : Nat := 0x58824447b308cb420c80e0a8209d080102102f0400c406188001300e8814c0391000001c829846620806c201300e8800130829820250812404a0a61e104098205e82f040000006a0ac5007c203b840000000c16e0a918e300b8414a100178205e0817820b20800003504080f012823860a601280b8604901c880000f040bc10026c20000000412800fb9ee3ca770ecdd0b8f714dadb3347650c8d8f3195f4ba16b2b7564a814727c4a08c50920d41080cff1ec39a6ecdb1b135869cd119d2e257ca694826c490891001f63d8788df1b42b8410630bc164238350600780c81401e02802800d6be6b66d8192530d6bd529ad8192530d6bdac9ad8192530d6be6b6ad8192530b5be7c5491a92530d7ad528ad1a92530a5fe7c5498a86530b5be7c54a4946530e7ad529262a4653087febc6689a54d20c6fd9a5ac9a54d20bed96c26d534c120ff489c54d524c120ff4953549814c120ded9539ad814c120dee9529ad814c120d7f18126d514c120ffc152605314c120fdaa7c54a4a4c120beba6c6064a4c120ff495354930a2520eed9534c16aa2520eee9524c16aa2520f7c9524c530a2520f7a95292d30a252087fcac56d3162520a6fe6c6055a8e520a6fd6ca255a4e520aebe6c6064a4e520e7ad52a264a4e520a7bd5ca264a4e520a7be8c5664a4e520d7b58192d3986520b3f68c54d8186520d7b58192d3a86520e6f66c6053a86520ff498354d5248110ff61835495148110a5fe7c5498a8e510adbe7c54a4a4e510a5fe7c54a8a4e510a5fe7c5498a4e510b5be7c54a4a4e510e7ad8254a4a4e510a7be8c54a4a4e510a7bd8c54a4a4e510e5be7c54a4a4e510e7ad5292a2a4e51087bdaca6d819253096be6c62d1a9253087bfbc9258a46530c6be499ad8a4653086fdbc9ab9a6052086ffbc9a99a60520ff095354a4a4c120f7495354930a2520f3d1814c53062520a6bd6ca264a4e520a5be7c5664a4e52087f5aca6d818652085fdbc9eb9a5491085ffbc9e99a54910fd627c5495148110a6be6c6264a4e510c3f68a86d8a4e510c6be6b92d8a4e510c7765a86d5a4e510a6be6c62a4a4e510a5be7c54a4a4e510
def j249 : Packing := (69,5,8,0,0,11,0,j252)
def j251 (i : Nat) : Nat := 0x30500000281800000e0a8248100120000000000
def j253 (i : Nat) : Nat := 0xcc41002789d28502a97cfaa94d6c0c92985f925b49c54d524c120ef24a9aa535b0298241fd09539f15292930483dc92a6a9260b551290496f9f58c54a4a4e510
def j250 : Packing := (6,6,8,0,0,6,0,j253)
def xusamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5d08196a6ab94f2cc0a2ac25680a4208344800af404600baf816401410012b19a81841c60c000c42020805074b337509a3308401433e21f673,0xd0800682ea0c92840000c0048172150480931233116251411ce40830401291860184746083044020a0801024b220801232884808224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd845701f1d11913202dc0733613022d37320007400800ad1afe020260200042200c22a0182ce0e23c1a30c625943a822604c0ef4400c8c6487f,0x180450191c01810002588723414c8c02232008a5840c9da018e001c34a80042210c21a81837c418141120c6259418c644008042442088c44829),(0x24838aa0756a21466e610150ba833388387300602bdb8190000420200120421c041c13c6063acc2b68c012038e7c000204603082518f1078f9c,0x24038ba0014e004660200050988072894082174842410058c50060381174421c001c0546040082603ee110010028109a0470218011471038514),(0x197c742262611d0db214d4442210696c0a51cd90211b80201007090088c098c000603967fd2100181402e03c0e0000a007807e0da9f01f80fe0,0x194874026221140882068084264d01702b41c810a41a00a00a3e0f44420a18c0026020a1513105064002e2580e0024208300de050ab00b00ae0),(0x24239f791d94e161f9b06f2bd910880890006d8ccca42002000100228941cd201b010e18010000c4004c003fe000c10007ef000dbc401fff000,0x24230b791d14e16179b06f3bd91288089008248d48e49506b4c100b38d95c52019101b08040c4ab9965d0027d000d35c04cd0100b44014ed000),(0x9292ca9480cd64d0bf20125add4044a265eb203100058084008c4f9441f200001eec0000000b000005efd800080df7bf810800597bfe000000,0x12924a94800904c0bb20102a85c0548225204a14442950806e00b35419b280001ea60000530a0a7504b5b4000000132e8000105959da000000),(0x336b26e0e8f854fcc5a748cca028013148c3c0162820064c00763206330137dfe00020000004b300ab010000010001267fef3ff000000000000,0x236b24a0e0f8547cc5a748cca0231131484bd7126873001c271e2e14151bbac94a0024000401bc3eb801020000002392bff7bbd008000000000),(0x3adc5057929368b0852dfca4026310028d2dc2073ae461020007108a80325000041000800010f000294effbfef7fc8090000c00262000000000,0x1ad45056929168b0840dfca4022300168d2dc806b9bc62a7381f94c2ae0090001e011080000f5d188114a4beffd7ee450000c00a6a000000000),(0x696cb5c93062b8b3008b689c98c626490e3304010243c24501a9b52b4ad77dfe1eeca3ffac10110161000000100c8850000410260000000000,0x4948b5411062b8330081610118062869480204813042a41d000d08a28644536b4159b5eaace424006b000001180d84d0000000a60400000000)]
def xucolumns : List z35 := [(64,0,447,0,13),(128,0,383,0,13),(16,0,495,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(32,0,479,0,12),(256,0,255,0,12),(8,0,503,0,12),(83,0,428,0,7),(66,0,445,0,11),(17,0,494,0,11),(132,0,379,0,11),(24,0,487,0,11),(9,16,486,0,8),(9,0,486,0,8),(7,0,504,0,7),(134,0,377,0,8),(3,0,508,0,9),(21,0,490,0,7),(320,0,191,0,11),(160,1,332,18,6),(132,2,312,65,6),(156,0,355,0,7),(28,0,483,0,8),(36,128,347,0,8),(260,0,251,0,8),(344,0,167,0,7),(264,0,247,0,9),(96,1,396,18,6),(130,1,332,48,6),(24,4,353,130,6),(133,0,378,0,7),(14,0,497,0,7),(258,64,189,0,8),(160,0,351,0,11),(296,0,215,0,7),(260,8,227,16,6),(112,1,396,2,5),(200,4,305,2,5),(388,8,99,16,5),(288,0,223,0,9),(0,16,486,9,10),(336,8,163,4,5),(26,4,353,128,5),(0,64,189,258,10),(168,256,23,64,5),(224,256,23,8,5),(88,256,135,32,5),(56,0,455,0,7),(56,256,135,64,5),(35,0,476,0,7),(26,0,485,0,7),(196,2,312,1,5),(266,64,181,0,5),(384,8,99,20,6),(276,8,227,0,5),(98,1,396,16,5),(19,0,492,0,8),(321,32,30,128,5),(160,256,23,72,6),(32,128,347,4,9),(256,8,227,20,7),(42696,4,305,2,5),(448,32,30,1,5),(0,128,347,36,10),(4,128,347,32,9),(53842,1,396,32,5),(35,128,344,4,5),(388,0,123,0,7),(268,0,243,0,7),(400,8,99,4,5),(168,0,343,0,7),(21,2,424,64,5),(194,4,305,8,5),(198,0,313,0,7),(448,0,63,0,8),(324,8,163,16,5),(176,1,332,2,5),(43408,8,99,4,5),(74,4,305,128,5),(43744,256,23,8,5),(148,8,99,256,5),(200,256,23,32,5),(43714,4,305,8,5),(33,0,478,0,9),(256,64,189,2,9),(258,0,189,0,8),(2,64,189,256,9),(74,0,437,0,7),(162,1,332,16,5),(49,0,462,0,8),(281,0,230,0,5),(6,16,480,9,6),(128,1,332,50,7),(0,32,94,385,8),(0,8,227,276,8),(1,16,486,8,9),(36,0,347,0,8),(16,2,424,69,7),(84,8,163,256,5),(256,32,94,129,7),(289,0,222,0,7),(16,256,135,104,7),(82,1,396,32,5),(42648,4,353,2,5),(64,1,396,50,7),(7,16,480,8,5),(385,32,94,0,5),(64,4,305,138,7),(129,0,382,0,9),(3,128,344,36,6),(292,128,91,0,5),(48,256,135,72,6),(136,256,23,96,6),(133,2,312,64,5),(152,4,353,2,5),(146,4,353,8,5),(257,0,254,0,8),(66,1,396,48,6),(320,8,163,20,6),(72,4,305,130,6),(34,0,477,0,8),(321,0,190,0,7),(84,2,424,1,5),(177,0,334,0,7),(25,0,486,0,8),(272,0,239,0,9),(1,32,94,384,7),(18,4,353,136,6),(322,0,189,0,8),(4,8,227,272,7),(24,256,135,96,6),(154,4,353,0,4),(197,2,312,0,4),(39,128,344,0,4),(273,32,78,128,5),(340,8,163,0,4),(144,0,367,0,11),(15,16,480,0,4),(114,1,396,0,4),(85,2,424,0,4),(178,1,332,0,4),(272,32,78,129,6),(202,4,305,0,4),(275,64,172,0,4),(20,0,483,0,8),(120,256,135,0,4),(132,8,99,272,6),(288,16,198,9,6),(297,16,198,0,4),(48,0,462,0,8),(272,8,227,4,6),(356,0,27,0,4),(355,0,156,0,4),(167,0,344,0,4),(416,0,95,0,8),(144,1,332,34,6),(384,32,94,1,6),(449,32,30,0,4),(232,256,23,0,4),(80,0,431,0,11),(141,0,354,0,4),(157,0,354,0,4),(404,8,99,0,4),(256,16,230,9,7),(257,32,94,128,6),(416,64,29,2,5),(80,256,135,40,6),(401,32,78,0,4),(67,0,428,0,7),(181,0,330,0,4),(480,0,31,0,7),(320,32,30,129,6),(128,8,99,276,7),(185,0,326,0,4),(66,4,305,136,6),(329,16,166,0,4),(16,8,227,260,7),(192,0,319,0,11),(16,4,353,138,7),(428,0,83,0,4),(152,0,359,0,8),(128,32,94,257,7),(24,128,323,36,6),(264,128,83,36,6),(334,0,177,0,4),(7,128,344,32,5),(21,128,330,32,5),(133,16,354,8,5),(128,256,23,104,7),(16,32,78,385,7),(12,64,177,258,6),(64,32,30,385,7),(199,0,312,0,4),(56,128,323,4,5),(168,16,326,1,5),(128,2,312,69,7),(265,0,230,0,5),(208,0,303,0,8),(320,16,166,9,6)]
def xuautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xulevels : Nat → Packing
  | 14 => j155
  | 13 => j156
  | 12 => j157
  | 11 => j158
  | 10 => j159
  | 9 => j249
  | 8 => j250
  | _ => z38
def xuindex : Nat → Nat → Option (Nat × Nat)
  | 14 => z15 6 53 6 10 2 4 j160
  | 13 => z15 22 107 7 13 5 4 j161
  | 12 => z15 142 533 10 16 8 4 j162
  | 11 => z15 221 1001 10 17 9 4 j163
  | 10 => z15 34 161 8 15 7 4 j164
  | 9 => z15 3 13 4 11 3 4 j251
  | _ => fun _ => none
def xu14 : Forest := ⟨511,14,fun j => xusamples[j]?.getD (0,0),xucolumns,xuautos,xulevels,xuindex⟩
set_option maxHeartbeats 0 in
theorem j222 : z24 xu14 (z8 z113) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=5) ?_⟩,z14 (d:=2) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j31 : block xu14 14 0 1=true := by refine (z1 (ar:=9) (rows:=1) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j32 : block xu14 13 0 3=true := by refine (z1 (ar:=10) (rows:=1) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j33 : block xu14 12 0 30=true := by refine (@z10 xu14 12 0 13 17 (@z10 xu14 12 0 1 12 (z1 (ar:=9) (rows:=0) (d:=0) ?_) (z1 (ar:=10) (rows:=0) (d:=2) ?_)) (z1 (ar:=11) (rows:=0) (d:=3) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q282 : block xu14 11 0 64=true := by refine (@z10 xu14 11 0 2 62 (z1 (ar:=9) (rows:=0) (d:=0) ?_) (z1 (ar:=10) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q180 : block xu14 11 64 64=true := by refine (z1 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q84 : block xu14 11 128 59=true := by refine (z1 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q83 : block xu14 11 187 38=true := by refine (z1 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j34 : block xu14 11 0 225=true := (@z10 xu14 11 0 187 38 (@z10 xu14 11 0 128 59 (@z10 xu14 11 0 64 64 q282 q180) q84) q83)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q284 : block xu14 10 0 3=true := by refine (z1 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q283 : block xu14 10 3 64=true := by refine (z1 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q181 : block xu14 10 67 64=true := by refine (z1 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q89 : block xu14 10 131 64=true := by refine (z1 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q88 : block xu14 10 195 47=true := by refine (z1 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q87 : block xu14 10 242 64=true := by refine (z1 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q86 : block xu14 10 306 64=true := by refine (z1 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q85 : block xu14 10 370 57=true := by refine (z1 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j35 : block xu14 10 0 427=true := (@z10 xu14 10 0 370 57 (@z10 xu14 10 0 306 64 (@z10 xu14 10 0 242 64 (@z10 xu14 10 0 195 47 (@z10 xu14 10 0 131 64 (@z10 xu14 10 0 67 64 (@z10 xu14 10 0 3 64 q284 q283) q181) q89) q88) q87) q86) q85)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j82 : block xu14 9 0 21=true := by refine (z1 (ar:=9) (rows:=0) (d:=3) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q281 : block xu14 9 21 48=true := by refine (z1 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j126 : block xu14 9 0 69=true := (@z10 xu14 9 0 21 48 j82 q281)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j127 : block xu14 8 0 6=true := by refine (z1 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q274 : z28 xu14 14 := by
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
  · exact j127
  · exact j126
  · exact j35
  · exact j34
  · exact j33
  · exact j32
  · exact j31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseU14 : Impossible true (z2 511) 14 (vars 511).toFinset :=
  z26 (g:=xu14) (i:=0) rfl rfl (z6 z113 q230) j222 q274 (by decide +kernel)
theorem q229 : Known false z113 := j11 q230
def x31d6 (i : Nat) : Nat := 0x1a230180fd10fc20
def x31l6 : Packing := (2,1,2,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def x31d5 (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def x31l5 : Packing := (5,2,2,0,0,5,0,x31d5)
def q255 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec04a3a21f673,0x2a912c2212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8a05bac6487f,0x56291cc44829),(0x2f8585078f9c,0x309c463038514),(0x135b045f80fe0,0xb41b88b00ae0),(0x3507a41fff000,0x142e4354ed000),(0,0),(0,0),(0,0),(0,0)]
def q256 : List z35 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def j191 : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def j50 : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => z38
def j190 : Nat → Nat → Option (Nat × Nat)
  | 6 => z15 8 11 1 11 3 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨1055,6,fun j => q255[j]?.getD (0,0),q256,j191,j50,j190⟩
set_option maxHeartbeats 0 in
theorem j108 : z24 x31 (z8 z113) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=1) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j242 : block x31 6 0 2=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j243 : block x31 5 0 5=true := by refine (z1 (ar:=6) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q82 : z28 x31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j243
  · exact j242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl31 : Impossible false (z2 1055) 6 (vars 1055).toFinset := z258 (q:=31) (prior:=z8 z113) (z6 z113 q229) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j277 : Lower false (varsX 1567) (z2 1567) 7 :=
  z16 (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (z26 (g:=x31) (i:=0) rfl rfl (z6 z113 q229) j108 q82 (by decide +kernel))
def q142 := z9 z113 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j75 : Known false q142 := z5 (m:=1567) q229 j277 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j216 : Lower false (varsX 42527) (z2 42527) 7 :=
  z16 (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (z26 (g:=x31) (i:=1) rfl rfl (z6 z113 q229) j108 q82 (by decide +kernel))
def z108 := z9 q142 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z189 : Known false z108 := z5 (m:=42527) j75 j216 (by decide +kernel)
def v27 (i : Nat) : Nat := 0x1040a3fa21fd51
def v24 : Packing := (2,1,1,0,0,3,0,v27)
def v26 (i : Nat) : Nat := 0x40000
def v28 (i : Nat) : Nat := 0x102de54110
def v25 : Packing := (1,2,1,0,0,0,0,v28)
def q174 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1c017c36792839f673,0x6456218245928112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc38e7cc981ff26487f,0x1021104810085244829),(0x627e830e1e31c78f9c,0x474a42a0e1430838514),(0x207083f01fc1f80fe0,0x38b5bd5f00bc1780ae0),(0,0),(0x21c0103ffe001fff000,0x1ba9de7dba001eed000),(0x5818003fffffe000000,0x6fdeefb7eff7a000000),(0,0),(0,0)]
def q175 : List z35 := [(96,0,15,0,4),(1,32,78,0,4)]
def j58 : List (List Nat) := [[],[32,83]]
def q260 : Nat → Packing
  | 6 => v24
  | 5 => v25
  | _ => z38
def j57 : Nat → Nat → Option (Nat × Nat)
  | 6 => z15 1 3 1 6 1 1 v26
  | _ => fun _ => none
def x111 : Forest := ⟨1135,6,fun j => q174[j]?.getD (0,0),q175,j58,q260,j57⟩
set_option maxHeartbeats 0 in
theorem q244 : z24 x111 (z8 z108) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=0) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j140 : block x111 6 0 2=true := by refine (z1 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j141 : block x111 5 0 1=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q20 : z28 x111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j141
  · exact j140
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl111 : Impossible false (z2 1135) 6 (vars 1135).toFinset := z258 (q:=111) (prior:=z8 z108) (z6 z108 z189) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j203 : Lower false (varsX 49775) (z2 49775) 7 :=
  z16 (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (z26 (g:=x111) (i:=0) rfl rfl (z6 z108 z189) q244 q20 (by decide +kernel))
def q27 := z9 z108 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q263 : Known false q27 := z5 (m:=49775) z189 j203 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j214 : Lower false (varsX 42607) (z2 42607) 7 :=
  z16 (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (z26 (g:=x111) (i:=1) rfl rfl (z6 z108 z189) q244 q20 (by decide +kernel))
def z41 := z9 q27 7 [(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(42739,[82,98,115,66,16]),(44981,[134,81,114,50,65]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z80 : Known false z41 := z5 (m:=42607) q263 j214 (by decide +kernel)
def x63d7 (i : Nat) : Nat := 0x344640ac3f865fc10
def x63l7 : Packing := (2,1,2,0,0,4,0,x63d7)
def x63h7 (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def x63d6 (i : Nat) : Nat := 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def x63l6 : Packing := (12,2,2,0,0,7,0,x63d6)
def x63h6 (i : Nat) : Nat := 0x24f9400060ba8030352
def x63d5 (i : Nat) : Nat := 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def x63l5 : Packing := (6,3,2,0,0,6,0,x63d5)
def x63h5 (i : Nat) : Nat := 0x20034000
def x63d4 (i : Nat) : Nat := 0x3b04813058432
def x63l4 : Packing := (1,4,2,0,0,0,0,x63d4)
def q253 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc87d813f01c73e21f673,0x765c43000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe10600dd66a4c8c6487f,0x3601a1ac64a488c44829),(0x238268c08738f1078f9c,0x9aa0e13831071038514),(0x16807e00f83f01f80fe0,0x125451e4502f00b00ae0),(0x1c109622ffc001fff000,0x2d89a218afc0014ed000),(0x690100fffffe000000,0x3f89a3bcfffdda000000),(0,0),(0,0),(0,0)]
def q254 : List z35 := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def j189 : List (List Nat) := [[],[65,50]]
def j49 : Nat → Packing
  | 7 => x63l7
  | 6 => x63l6
  | 5 => x63l5
  | 4 => x63l4
  | _ => z38
def j188 : Nat → Nat → Option (Nat × Nat)
  | 7 => z15 7 21 2 9 4 1 x63h7
  | 6 => z15 2 9 1 8 3 1 x63h6
  | 5 => z15 1 5 1 6 1 1 x63h5
  | _ => fun _ => none
def x63 : Forest := ⟨1087,7,fun j => q253[j]?.getD (0,0),q254,j189,j49,j188⟩
set_option maxHeartbeats 0 in
theorem j107 : z24 x63 (z8 z41) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=0) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j238 : block x63 7 0 2=true := by refine (z1 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j239 : block x63 6 0 12=true := by refine (@z10 x63 6 0 7 5 (z1 (ar:=6) (rows:=0) (d:=1) ?_) (z1 (ar:=7) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j240 : block x63 5 0 6=true := by refine (z1 (ar:=6) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j241 : block x63 4 0 1=true := by refine (z1 (ar:=5) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q81 : z28 x63 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j241
  · exact j240
  · exact j239
  · exact j238
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl63 : Impossible false (z2 1087) 7 (vars 1087).toFinset := z258 (q:=63) (prior:=z8 z41) (z6 z41 z80) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j267 : Lower false (varsX 6719) (z2 6719) 8 :=
  z16 (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z53 (prior:=z8 z41) (z6 z41 z80) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def q132 := z9 z41 8 []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j61 : Known false q132 := z5 (m:=6719) z80 j267 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j279 : Lower false (varsX 1087) (z2 1087) 8 :=
  z16 (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z26 (g:=x63) (i:=0) rfl rfl (z6 z41 z80) j107 q81 (by decide +kernel))
def q144 := z9 q132 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j78 : Known false q144 := z5 (m:=1087) j61 j279 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j219 : Lower false (varsX 11327) (z2 11327) 8 :=
  z16 (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z26 (g:=x63) (i:=1) rfl rfl (z6 z41 z80) j107 q81 (by decide +kernel))
def q36 := z9 q144 8 [(2719,[117,101,67,32]),(13495,[115,84,99])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q273 : Known false q36 := z5 (m:=11327) j78 j219 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j276 : Lower false (varsX 1599) (z2 1599) 8 :=
  z16 (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z53 (prior:=z8 z41) (z6 z41 z80) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def q141 := z9 q36 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j74 : Known false q141 := z5 (m:=1599) q273 j276 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j205 : Lower false (varsX 47679) (z2 47679) 8 :=
  z16 (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z53 (prior:=z8 z41) (z6 z41 z80) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def q28 := z9 q141 8 [(47679,[]),(44127,[101,66,16]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q264 : Known false q28 := z5 (m:=47679) j74 j205 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j215 : Lower false (varsX 42559) (z2 42559) 8 :=
  z16 (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z53 (prior:=z8 z41) (z6 z41 z80) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def q33 := z9 q28 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q270 : Known false q33 := z5 (m:=42559) q264 j215 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j202 : Lower false (varsX 52799) (z2 52799) 8 :=
  z16 (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (z53 (prior:=z8 z41) (z6 z41 z80) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def z72 := z9 q33 8 [(44719,[116,100,83,32]),(54967,[115,84,99])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z105 : Known false z72 := z5 (m:=52799) q270 j202 (by decide +kernel)
def v21 (i : Nat) : Nat := 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def v16 : Packing := (5,1,3,0,0,7,0,v21)
def v19 (i : Nat) : Nat := 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def v22 (i : Nat) : Nat := 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def v17 : Packing := (10,2,3,0,0,7,0,v22)
def v20 (i : Nat) : Nat := 0x700009040000000000ddd0800002
def v23 (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def v18 : Packing := (3,3,3,0,0,5,0,v23)
def q172 : Array (Bits × Bits) := #[(0x98543c01121d833f4fc,0x1e6c550011215802a4ac),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc268201f82067f2cc8cf,0xa9854a582041528c8ca),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6400c361c3861cf0f0f,0x146729421c3060870605),(0x25004de0e03f81f00ff0,0x219082bde00e81700950),(0x18979200ffc001fff000,0x9328e7ca8001fd5000),(0,0),(0x103ab009fffffe000000,0x35648318357bea000000),(0,0)]
def q173 : List z35 := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def j56 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def q259 : Nat → Packing
  | 7 => v16
  | 6 => v17
  | 5 => v18
  | _ => z38
def j55 : Nat → Nat → Option (Nat × Nat)
  | 7 => z15 23 29 4 12 4 4 v19
  | 6 => z15 2 11 1 10 2 4 v20
  | _ => fun _ => none
def x189 : Forest := ⟨1213,7,fun j => q172[j]?.getD (0,0),q173,j56,q259,j55⟩
set_option maxHeartbeats 0 in
theorem z237 : z24 x189 (z8 z72) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=1) ?_⟩,z14 (d:=2) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j137 : block x189 7 0 5=true := by refine (z1 (ar:=7) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j138 : block x189 6 0 10=true := by refine (@z10 x189 6 0 3 7 (z1 (ar:=6) (rows:=0) (d:=0) ?_) (z1 (ar:=7) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j139 : block x189 5 0 3=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z141 : z28 x189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j139
  · exact j138
  · exact j137
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl189 : Impossible false (z2 1213) 7 (vars 1213).toFinset := z258 (q:=189) (prior:=z8 z72) (z6 z72 z105) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j272 : Lower false (varsX 2237) (z2 2237) 8 :=
  z16 (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (z26 (g:=x189) (i:=0) rfl rfl (z6 z72 z105) z237 z141 (by decide +kernel))
def q137 := z9 z72 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16]),(12477,[32,83,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j70 : Known false q137 := z5 (m:=2237) z105 j272 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j275 : Lower false (varsX 1725) (z2 1725) 8 :=
  z16 (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (z26 (g:=x189) (i:=1) rfl rfl (z6 z72 z105) z237 z141 (by decide +kernel))
def q140 := z9 q137 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j73 : Known false q140 := z5 (m:=1725) j70 j275 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j270 : Lower false (varsX 2749) (z2 2749) 8 :=
  z16 (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (z26 (g:=x189) (i:=2) rfl rfl (z6 z72 z105) z237 z141 (by decide +kernel))
def q135 := z9 q140 8 [(2749,[]),(1371,[130,50,98,82,115,33,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j68 : Known false q135 := z5 (m:=2749) j73 j270 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j210 : Lower false (varsX 43197) (z2 43197) 8 :=
  z16 (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (z26 (g:=x189) (i:=3) rfl rfl (z6 z72 z105) z237 z141 (by decide +kernel))
def q31 := z9 q135 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q267 : Known false q31 := z5 (m:=43197) j68 j210 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j208 : Lower false (varsX 44221) (z2 44221) 8 :=
  z16 (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (z26 (g:=x189) (i:=4) rfl rfl (z6 z72 z105) z237 z141 (by decide +kernel))
def z126 := z9 q31 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(42843,[130,50,98,82,115,33,65]),(48102,[115,83,82,130,99,66,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z243 : Known false z126 := z5 (m:=44221) q267 j208 (by decide +kernel)
def v1 (i : Nat) : Nat := 0x60bfd31
def v0 : Packing := (1,1,1,0,0,0,0,v1)
def q168 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0021ee01fffe490e402109fc2670e40ff27f,0x208080808080490a402108a80450a401222a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe488e110001fe0033fcc6313cd9833fca4c4f,0x156067666666600212cc63114910212ca4c45),(0,0),(0x1000fe000071c380f83e331e1c38f38f8c,0x66caaaaaaaaa718380f82c321e1838a38b0c),(0x1000fffe0181fc0f003fc3e01fc0fc0ff0,0x199355555555580740f001341e007405c04d0),(0x1b761ee000001fe000fffc003ffe000fff000,0x1036e0f1e1e1f24000a948003fba000fed000),(0x488e11000001fffff0000003ffffff000000,0xa9f989999999ffded00000036efded000000),(0x1b74000000001fffffffffffc000000000000,0xfc91f0e1e1e0dbfff56b7ffc000000000000),(0,0)]
def q169 : List z35 := [(88,0,163,0,4),(8,0,243,0,7)]
def j52 : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def q257 : Nat → Packing
  | 7 => v0
  | _ => z38
def j51 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : Forest := ⟨1275,7,fun j => q168[j]?.getD (0,0),q169,j52,q257,j51⟩
set_option maxHeartbeats 0 in
theorem j224 : z24 x251 (z8 z126) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=0) ?_⟩,z14 (d:=1) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j131 : block x251 7 0 1=true := by refine (z1 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q276 : z28 x251 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j131
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl251 : Impossible false (z2 1275) 7 (vars 1275).toFinset := z258 (q:=251) (prior:=z8 z126) (z6 z126 z243) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j204 : Lower false (varsX 48891) (z2 48891) 8 :=
  z16 (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl251
    (z26 (g:=x251) (i:=0) rfl rfl (z6 z126 z243) j224 q276 (by decide +kernel))
def z73 := z9 z126 8 [(43479,[115,83,133,99,50,66,16]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32]),(48382,[32,67,117]),(49403,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z140 : Known false z73 := z5 (m:=48891) z243 j204 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl127 : Impossible false (z2 1151) 8 (vars 1151).toFinset := z258 (q:=127) (prior:=z8 z73) (z6 z73 z140) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j278 : Lower false (varsX 1151) (z2 1151) 9 :=
  z16 (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (z53 (prior:=z8 z73) (z6 z73 z140) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def q143 := z9 z73 9 [(18814,[129,98,82,16,66,49,112]),(1271,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j77 : Known false q143 := z5 (m:=1151) z140 j278 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j209 : Lower false (varsX 44159) (z2 44159) 9 :=
  z16 (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (z53 (prior:=z8 z73) (z6 z73 z140) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def q30 := z9 q143 9 [(52959,[32,67,117])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q266 : Known false q30 := z5 (m:=44159) j77 j209 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j213 : Lower false (varsX 42623) (z2 42623) 9 :=
  z16 (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (z53 (prior:=z8 z73) (z6 z73 z140) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def z57 := z9 q30 9 [(60285,[129,82,113,48]),(42743,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z70 : Known false z57 := z5 (m:=42623) q266 j213 (by decide +kernel)
def j264 (i : Nat) : Nat := 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def j262 : Packing := (10,1,7,0,0,9,0,j264)
def j263 (i : Nat) : Nat := 0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def v11 (i : Nat) : Nat := (if i<1 then 0xc845e2d1218282a8801c24251480104a170b0541d28c2411f02104a1f15004282d1700020915c80581f207008240f85e2d150d894222f00304a1f088046607001c0633148045e2e160a9108128a88e1f1681c008088a80f00000845a2f40a88e250f8cc0e0038045f1e19874a0415044022d120a4000248105c111500428400000923114910570008840e26128c8562f93800e1b1289054010387052411680161412046040702004800048984a240f8ac5f220020222a0607c4a290380110703c845a2f28a8502b900b03e6154045f200f944a1f1501c021c0d8545c2d002c381b8a87c54071285852005094481f15044722f1588920180002512715981e1f150045207001c08240f844020f0a44066005002502b13901e2d150045200081c55281589c48503014550203810022900249a4c0e8943e07001c2e1c0d8904a1f8b4542200505c381b120943f168a84400a2407036251207e8315088014430e06c4a240fd062c110028381b0b894481f8b454220050d86a14078903e108904400af98fbdbd0be5cf07f72fb57d79e9af3eb9c7c57e00ef1b73bb74d9cec1f551a6dd1de7df379978c9ee4531d789ec2460a2fed7a0bc05c86df16bdb4a59aec2b5daacb554aa654e5a50d10a8213c39d64d7e65b2e994e49f24cb22a8dcc61e2e115088ac3d61750a3838c0da008fd27d03d4de0ce9e728b8e9c22db26a9b3f593cc3f606af4970ab535952b51556a3a4fb26a52b890f465a2650867ed3d49d94dfa6a732d1834bb65a02b7141894e45120b0f486e634a1830b504fc23a0ed85f023a0be02f8003fe90287ff54140ffa64a07fd71083fe90281ff5c940ffaa2187fd30503fea9281ff5d940ffae6a07fd6454ffea02a7ff4c110ffac0187fd63083feb1a21ff48063ffa42887fd72443fe900a7ff44153ffa84887fd54503fe98aa7ff50540ffaa6107fd61503feb02a7ff4c420ffaeaa07fd20443feb1aa7ff58d40ffaa2207fd62503fe39281ff58040ffa40a9ffd42503fe90061ff4c910ffae2a9ffd61103fe90081ff4c510ffa20107fd5150ffeb8a81ff58430ffac0a1ffd5054ffe982a7ff5d153ffae8887fd54443fea0aa7ff5cd10ffae6107fd30083feb0063ff1c153ff8e4887fd40443fea9061ff54831ffaa4207fd7054ffea0a21ff54540ffac0a07fd31503fe90041ff50020bfae4885fd7150fdea1081f758d53bfae0a1dfd71083dea0a817f5c153bfae2185fc72503fc902217f5d830fea82885fd72102feb90c77f1c910bfae031dfd7154efeb88c77f5cc20bfaea18dfd760c6fe382a7fe4c140bfaea205fd720c7ee982877f5c453fba60a9dfd74442feb9a217f5d840bfae2205fd7550efeb92817f5c053bfae4187bd54502feba8617f5d540bfae018df57114ef6b90815f5d440beae2204fd76102eeb98813f5d830 else 0x4963e2311400a4a1a0a4582712184c241287c662c158bc84270e801840148cc584020aa002813c1c560040d250001449c4e2b3c00522d18903e00190acb0116c005c2b1609ce34940b858271598642b11084c021089c484b1c0b8562d178880e0078d0421f1c0bc582413801230100bc53070f987e10800b482a160b85e4181145e2c1007cd258f8220f0028187c051412440250f80c08a1801240208f87cd258f8320f0028c04238178b0401f38805707178a43e60e8d059010009c5672241c5a21038bcc1f008b0564150b05a2f20d08100170b0502b13a02020138ba020717c005a9150cc5e31a4a058271594602a900823e1f83c00089039145e31a07c5901130ac5e4613801411800a45a4170ac802c1309cc34170c85841f906002d2010222a83c00422d228bd22c808744f0715987e128f8c4522d801c4033210f85e290f9c422d178e3616928bc5c2916c0103f0b47c622916c00e0518080422f1f01053070fa85c2f180a45859247c5e2d1588c450040b0562094524a33170b4210040f45c2f11400a3c108a45e24000b4e211241c5701038005e8178e05a30f8b04301c0ac58200f98763a1089449070f8bc562d1c80183017c80401f28cc5e20e8ac5e3820cc5d0101400c071c0b462f17004602916183e2c10405900000b4b04160b6020280182a2c800005a590884002d17946e050207c5851a0a6002d160a0562740d0582e15c06000013a06824140044a27838cc641f002c6230018bc5c2d1584502c158861200247c826120943e111508e442b17aa2c1c0d8904a1f8a8bc560051248420138b400451781d226128c854011207e442b17aa3d1d018040e00200a4662c50024e28160aca2a03)
def v2 : Packing := (122,2,7,0,0,13,0,v11)
def v7 (i : Nat) : Nat := (if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def v12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xd855c830fdd314c140dfd7254830dfd7650020bfd855d110f7d5250553ff9614c140fdd3050553dfd754c420dfd7348020dfd745c910dfd7550020dfd511c940dfd635c910bfd821c153dfd8748063ff5514c910ff98448110dfd735c910dfd205c453bfd855cd10bfd8258031efd6058430dfd7244153ff92058030dfd405c910dfd7254140ff48148143dfd7250553dfd825c053bfd864c140dfd515c143fdd304c510dfd7158940ff93048110dfd855c831dfd405c553ff9204c140ff48148153fdd3044153dfd605d110bfd831c910ff48148140bfd865cd10fdd6350553dfd764c510bfd8348110dfd7248030dfd714c020fdd534c140dfd205d440fbd5450110dfd615c143bfd8550510dfd7258030fbd4050553ff98348110ff92058040fdd3059153dfd855c8409fd825c0539fc87589409fd8758c209fd87589409fd861c940d7d525d4409fc8754940f3d54541409fc87545409fd825d4309fd831c910ddd7358c209fc8759153f5d524c153ded615c840ddd205cc40fb9544c1409fd805c5539fd8758d10f9c844c153cfd615d830ddd7354c20bdd8358153ddc835c9409fd825d5439fd835c910df5615c440dbd425d543fb541585409fd815d840df9205c0639fd825d540d7d525d5439fd8754c20cfd815d830cfd615d8409fd841c910cfd605d8319fd851c940ddd305c543bf581551109fd805d831fd9534c140df5205c453ded805c8409fd825d440d7d825d440d7d525d4309fc874c540df9724c140ded855c840cfd605d830ddd305c5539fc8744153ded605c8409fd815d440ddd515cc40ded7254840df97348110fb9414c1409fd874c940df4815c940d7d615d440ddd525cc409fd821c153cfd525d840cfd605d8409fd811c940df5411c910f9d424c143d7d521c1539fc8748153dbd425d8409fd841c153afd861c1539fc8758d10dbd425c440edd6358153f3d52551409fd805c863fe94248110dbd425d440fd9634c140f5d5258d53fb54150110cfd515d840df5515cd10d7d205d440fd93048153df57154440ded7254830fb5414c540ddd635c1539fd855c543df5605c4409fd811c1539fd874c420f5d5458d53d7d515d430cfd205d830ddd615cc409fd815d540dbd7255140ddd605cc40df5714c4209fc8750153df5205c440ddd305d5439fc874c910df5865c440df5525c440edd6359153fb54250510f3d5450153ff141481109fd815d830cfd815d8409fd825d4319fd8750940dbd7250540fad4248040df5855c4409fc8750910cfd515d830fd9204c1439fc8758540d7d515d440bbd81551409fc8755110cfd205d840cfd525d830fd9314c140df57154430d7d815d440ddd734c420d7d605d440ded515c840d7d525d431df9205c0539fd815d430d9d425cc40cbd425d8408fd861c153d3d425d440db5425c440 else 0x4a2c4cae62b34ab42a44a6e288ca0a279c9ce265c96a251c91a23b48d4229c87a20e47f81f7c7b21e147621d246fe1b946b819dc64a18c460e17d45c8166c56e152c51e13c44d812ac488119444210543f20f143980d5c33e0c6c2ee0b0429e09c424e08ac1fe079417c049c0d201a4000bfd8148143dfd7254940ff56150540fbd4254543dfd7158c20ff92058d10dfd8748053bfd8255110efd6058d40dfd8748153dfd7154c20dfd205d540dfd755d110dfd7159153dfd205c543fbd4250510dfd205d430dfd865c440fbd4254440ff92058153dfd825c063ff9205d110dfd205c053ff92055110fdd3048153ff55150510bfd861c940bfd8058940dfc825d540bfd811c153bfd864c510fbd4248040fdd2058d53dfd7254440bfd8258430dfd205c143fdd204c143dfd205d840ff48148063efd6158140ff92044153dfd215d540dfd764c420ff94248110ff48148053bfd835c910dfd7148020dfd835c910bfd8158040fbd5250540ff5514c553dfd764c910dfd7154830dfd7348110bfd8448110fbd4158940ff5514c110bfd8148063dfd615d440dfd305c910f7d5255140fdd3054543dfd7258140fbd4254840dfd605c840bfd8148053dfd605c031ff53148510fbd4255110ff48148030fbd4158d40dfd525c143dfd7248140dfd755cd10bfd851c940ff55250510fbd2050540fbd544c540dfd7650110bfd8058430ff92058143f7d5254543dfd754c020ff55150110ff92058140bfd8258440dfd7158030dfd205c153dfd7148030dfd7258d40dfd535c910f7d5244153ff5514c420ff5415c910fdd3258d10bfd804c940dfd865c031fdd314c940ff9514c140dfd7044153bfd8254543bfd8058d10ff9204c910dfd7650510dfd7258430dfd525c831efd6158040fdd604c143bfd8054543dfd7348510bfd854c940ff5515d110dfd7254840dfc725d540dfd865c430dfd205d830dfd605c543dfd764c020fbd2055140fed2054940bfd8158d40dfd525cd10ff48148020ff5515cd10dfd7154840dfd765cd10dfd205d543ff54148110dfd7154140bfd8258143ff94048110dfd805c863dfd7344020dfd605c440fbc8255140bfd8258153dfd525d110dfd7254430dfd205c840dfd605c831fbd4250553dfd105d540fed4248110fdd3058d10fdd634c940dfd8748143f7d5254540dfd205c863fdd524c143f7d5250153dfd7258540dfd765cc20dfd205c440dfd755cc20dfd764c110efd6058d53ff5514c510bfd845c910ff5514c540dfd541c910ff9524c140fbd4258040dfd205d110fbd4158140fbd4154140dfd205c063dfd724c540ff9205cd10dfc8748153dfd205c553dfd615c840dfd7254540dfd525c031fdd634c140ff48148040dfd205c463ff9604c140dfd605c143ff56150553fbd4258440fbd541c940bfd8054831df) else (if i<3 then 0xe31382b14371285e1485b0019158003d0b48170621485e1585a60b82d12821685c30b42e0b03320021605e30742b0002f200e1688110a82e0e080042a170c2c0ac41c05a21142c105c0f84a0042c501d000b42e24001385a3006070a42d800b0223e20902b07000904a15a4e0005e40bc2d1058158a000a42d185d0fa4030fd1687c310a42d800e1685e2400290b460005a28d033004000aca038001685e40442d0bc61fa830005a40bc318402c20661788070002d0bc814c000005a487d120c42e0b60034371285e1485b0018330b451380e0005640fd418002d20561505e30b045107e0b43e1885216c0070442f105c1985216121b8942f0a42d800c8ac001e85a40b82f105e0f85630ac2d1008158028f902d800320b8816c001905c401c3d0b46008002705648a0010002b223e158811800290b4817052178e000a42d1c4b0005e30b42f1002c24001485a34a0110b42b2022170581c121f0c5160b42e800c1705a24a0000bc614a000005a4046000a42d20021585e30fc418002d24001485a3008000b4712c3f03c0040a42d10380de2c1204a0fe2a0005e15ab160902507c2f0002e0ad01882008c88160561705a80731506c240941fc58000bc2b56820e0361204a0fe2a0005e15ab1c4c65f17ec59714cc4cf124c3df0dec2ef0a2c1ff066c13702abff6fe4bf7efc6beb6f9ebe3ef76bd9ef44bcaef12bbbeeeabb46eaeba56e68b93ee36b84ede6b70edb4b646d82b5a6d50b4ded28b466d00b3c6cd8b2d6ca6b20ec60b0cec10afdebdeaf3ebb6ae76b7aad86b34ac46ae4ab56abcaa66a76a9c6a4ea8aea08a7e69e0a6f699aa5de954a4ee922a4268e6a35e8b4a26e882a156832a0167ec9f767ce9ed67a69e3677e9d967389c7e7069b8e6d49ac668e99d665298be61697a65c696de594963e58a959e54494864f4934649a91b6468911642290263c88e9638c8da63508d063288c162e28ad629289e626a88f621a88061d486ee1988626166853612a84460ee83560b28266080819e04480d60127f95fb87e55f7c7d8df547cc5f0e7badee67b0de9679cde4678b5e287815de2774ddb07635d74756dd4c74a5d1a7405cfc738dcca72edca27225c70715dc3e7095c0c6ff5be46f05bb26e3db806d9db4e6cadb126be5ad66b1daa46a55a726965a4a68c5a0467d59dc66e59b4669599665f596e652d92864158ec63758c462d589261e5860611d824602d7e85eed7a25e4d7665d0d72a5bcd6da5a8d680599d644588560857955cc567d55e544d4f05335496521d45a510542850153e24efd37e4d6d3244bdd2c04a4d270493522047cd1da46dd19e461516244fd12643bd0a4420505440ed00e3facfc83e94f8c3dccf463c64eec3afce9c39e4e5638f4dfc373cd8e35d4d523494d023354cbc323cc6c314cc3a3084bea2ef4b9a2d8cb else (if i<4 then 0xb440005c248e000006918570000044582d0b878004274042b185e10cc2d105a17891f0bc580041f085802091f08521709270b02d18001108330bc708058168c2a8042f40080f858158c400b0415c3e200021485a247c00104e0380030ac2d12028044e1692150b900187ea085c1690000c0014880407c3318520f856302021600034882d0b8714008800e1f08581689200b02d182216056341c2b000613856000c2e0a441705e20882f143a1585a30ac213c00800c000b841705224842a0b600224a0205834042b1142f207016881f0856147c2c104018002c105210cc2c10641585f00102d0b041689620a42f0b061785070ac001a4a1985c380040105c1485a34882b8006168002810250a82f204e1605a30b030aa00000c004482d0b8691056168e1d0b42f1a51038561692070ac2d1868808590005e54802d8002e201200a61f1c2a1605a34821f12461c0221585e1699000b02b185816883d0bc381a0016083308561788290b82d185c1580030842e0e02d22401685c30a42d122c140a040b82d20740005e30b02d123e1605680101f0b040e84e170c04084e1605a38003312440005a30bc0010568008030b42f143e1606230ac2f120f0f882d0e0483c3e148c1f08650005638042b0bc2d224e17c000012410b9001856160a270b441685088000018561786630c21f0bc600842d0bc70dc4a1705e4400290ac6814081685c40ac001022587c331a4f000003488283c00000c2f4002e185816882d10048805010ac2c1c2010ac2d1002f000417c0020ac21485e240033105616082c0b441785a21142f10701688040884148a0447c041a3e18961f0a4616042e0a441705220802c0bc61705a20ac001048148563c0028385e160c29084f0000030a42f105810ac2c123e0fa001790400858178928800001802c0a4010b02f105810c0290b0622a0e000d070bc00185e160833085817882b08221485a30b02d105e20082d0b050805c168c2c0b448f85e020e414582e0bc817856245420085a1740040bc4f0b061485e200407000290aca2005c24542c800000b4a1785c160c2b0b4408864270c070f42d18661788070b82f185c1c08070002f0b490dc4a178530005a60fd1687c310a42d800e0024e158c2d0002f1854038001705e50bc30005a0005c401c2f100e1788331142b180e1605a3000070bc70dc4a1785216c0060a82f0ac71a0508000313942d800320b8912c3e8440f001407004000b4817800168c2c0bc2d185b000641712000b4000b88178562008000b861705a20442f10221585a301c3d0b861685e28942987e07800a1fa2d0f8621485b001c070f42d1a2b0007a1690000b441705a1985840002f0ac68a87a168c100b42e18221788450b041fa830005a4046000a42d2023000521692150b0000b4902054178c004a02b18022705 else 0x5e000901402270b880080020bd0010581788300bc402042007c2c0b4813c0020110740061605a24a02a0b461605a212c2d10561e85e38101f0b00020521688015a0020b42e121010b03000522404310a0e168c2c0b4416056209c2b0b0600b02d10601605e38590012430385a171029)))
def v3 : Packing := (387,3,7,0,0,14,0,v12)
def v8 (i : Nat) : Nat := 0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def v13 (i : Nat) : Nat := (if i<1 then 0x9b9c399b91b8f38cb84b71b5eb5c359b4c349b3c32eb26b2431c319b11b04301aff2f1aef2e72e4ae22dfad7acfacd2bfab22afaa229a28ca7f271a69a61a5424c23ea31229226a1920ba039fb9f39f11e39d61ce1c61c39ab1a899b18817a97817596816015294514293513292512291510d0ff8fd0ef8e20df8cc8ca0bc8a989688e88687e87686906105384603e03081d81580d80047f661205c4538fec910eb1a21fb14161120443f2a8298a64a07ad5854158940afac8aa839221d3d525c954503b5a84902ea2047f661205c4638fec810eb22a7fa92050960103be122902e031efc4818155110f5aa0ac2b02819f92021d54443af240b02ea20779245805c840e9ea12c0ba881f993055131503db2c6b0260a067d261205c440df490304aa2215f5914817114ebbb22b02e62067d2058748143ecea12a2b988157d9158175103f3260a0282a9e5f549841c153cfa4090e902a75f5984817114e3fb2243ac8a9ff2481524c143cfa48b04b80a757d9258575103f6282b0a60a0767509525cc40edaa130cb88819f48161d2018ff6282a02408865f21d5244153cee43a60902a75f5972052014fbe2c0902e22047f261205c553eba48a40ba881fd1302052054fa7a84a92ea2065f549811c153e7ab030cb8881cf56158171103b5a84902e22047f6448748153edaa12e2a88819f4916017218ebeb2ab8a621076d509855c440fd2a11029008197c875494054fa7a84c12ea2073d245205d8408fec910ea8a811fd9221d1054f3e930902e229c7f6488755110ed690284bb081df0914817014fbaaa2b9a621076d5c54258040ecea1240b9881db5415d9404432f90ea92a2a072f509205d840e9ea1302ba881d9d42581731038fac2b02ea2067d5c58258440ef8a8ae690221d3d7550961102bdb22b02e42077a481605c840ebaa8aa4b9a21de92054973442beb24c32e22076d5857250540fd8a0a84902211fd9221d4054fa7a84a8aea2057b649615c840cfaa8b06392219bd4260575103b3ae6a12c2207ea4814255110afac8ac0b88815dd925857310376a82c0ac6a0775245205cc40e9ea1240ba881fd13054531503b6ae2a12c22057b661615c840e7a48a40bb061f994158d30503fc240a928288737585605cc40e76b0ac0b90819f48161d2014f3790ea12a88872f509515d840cfa40b0e902a7dd93021d2054fe72a8a9260a067d61c8148140edaa12a4b88819bd5421d31503b6a84902e2205fc2614148110fe89810290287dd92058173103ed2a490220a9f875915458d53fd090284a0a21cad4248176103f1240a1260a1c3f261525d8308fa4c240b88a787d526187054fe9240a9260a9c3f261525d840c6e43ac6b22a7d2d42481751033a90640ae4a0763509205cc40fc8a0a629828199c872113054fe3260aa280a9f69509205c440 else 0x10200423e30660b04100160900851382e80030561002b05a2c820b8580020448082b05a484e0b4404431058b02d18220a00102b000224e800400000082908015a0010290800000016840005e8005455000817a001001604006001683058168c1602f05a30028aa001001482d102905a243e10100080000415a001001455000800ac20000170700041904800a8b2001002702d1516082b4002a8280040a41688000417041790010290b1605a22400b840b820003000447c178800050004000400ad000817900102b08290821a10105e80080a2c80040c815a00182f200200017800102d082905a20520b44083e0ac40a0f4004024e8004c0034550008105900080202c102a0b1605a3002e05a240907c158c1721f056305e105a1052105a105e0b440b420b417890f82b102b0a1f05620000bc158c178417850f82b14f04edcdaccd4bfcb7ca4c9cc9a48cc7f47745ec51449436433c26418c0b408c063fe3f63f3be63de3dbbd93d6bd43d1bc9bc73c4bb73a)
def v4 : Packing := (137,4,7,0,0,12,0,v13)
def v9 (i : Nat) : Nat := 0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def v14 (i : Nat) : Nat := 0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def v5 : Packing := (19,5,7,0,0,8,0,v14)
def v10 (i : Nat) : Nat := 0x81900
def v15 (i : Nat) : Nat := 0xa3390a134a4c28290221e50549302048748153
def v6 : Packing := (2,6,7,0,0,3,0,v15)
def q170 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc402ee4723402700821075b301c73e21f673,0x516b7a00004108082102532000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9401c100011c87330c6249c366a4c8c6487f,0x38c8481ffffae3330c6248c164a488c44829),(0x133511089c9ec04010038e7c8738f1078f9c,0x4321b34000011cc010010028831071038514),(0x235800308c800883e07c0f80f83f01f80fe0,0x24960cb3b52cc103e0580f80502f00b00ae0),(0x604a2032204028fc007ff000ffc001fff000,0x5a69404c4ad32e7c0027d000afc0014ed000),(0x8800ec54221107fff800000fffffe000000,0x52a908506683ef6a59000000fffdda000000),(0,0),(0x8a410885023507fffffffff000000000000,0x2c5644af997c0015a6feffd7000000000000),(0,0)]
def q171 : List z35 := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def j54 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def q258 : Nat → Packing
  | 10 => j262
  | 9 => v2
  | 8 => v3
  | 7 => v4
  | 6 => v5
  | 5 => v6
  | _ => z38
def j53 : Nat → Nat → Option (Nat × Nat)
  | 10 => z15 177 223 4 13 7 2 j263
  | 9 => z15 185 697 7 15 9 2 v7
  | 8 => z15 39 199 6 14 8 2 v8
  | 7 => z15 11 35 3 11 5 2 v9
  | 6 => z15 1 3 1 7 1 2 v10
  | _ => fun _ => none
def x191 : Forest := ⟨1215,10,fun j => q170[j]?.getD (0,0),q171,j54,q258,j53⟩
set_option maxHeartbeats 0 in
theorem z133 : z24 x191 (z8 z57) = true := by
  simp only [z24,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=4) ?_⟩,z14 (d:=0) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j42 : block x191 10 0 10=true := by refine (z1 (ar:=8) (rows:=0) (d:=2) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j83 : block x191 9 0 48=true := by refine (@z10 x191 9 0 7 41 (z1 (ar:=7) (rows:=0) (d:=1) ?_) (z1 (ar:=8) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q290 : block x191 9 48 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q289 : block x191 9 84 38=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j132 : block x191 9 0 122=true := (@z10 x191 9 0 84 38 (@z10 x191 9 0 48 36 j83 q290) q289)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j84 : block x191 8 0 41=true := by refine (@z10 x191 8 0 5 36 (z1 (ar:=7) (rows:=0) (d:=1) ?_) (z1 (ar:=8) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q292 : block x191 8 41 36=true := by refine (z1 (ar:=8) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q291 : block x191 8 77 36=true := by refine (z1 (ar:=8) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q192 : block x191 8 113 32=true := by refine (z1 (ar:=8) (rows:=0) (d:=3) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q191 : block x191 8 145 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q190 : block x191 8 181 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q189 : block x191 8 217 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q188 : block x191 8 253 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q187 : block x191 8 289 36=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q186 : block x191 8 325 62=true := by refine (z1 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j133 : block x191 8 0 387=true := (@z10 x191 8 0 325 62 (@z10 x191 8 0 289 36 (@z10 x191 8 0 253 36 (@z10 x191 8 0 217 36 (@z10 x191 8 0 181 36 (@z10 x191 8 0 145 36 (@z10 x191 8 0 113 32 (@z10 x191 8 0 77 36 (@z10 x191 8 0 41 36 j84 q292) q291) q192) q191) q190) q189) q188) q187) q186)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j85 : block x191 7 0 53=true := by refine (@z10 x191 7 0 17 36 (z1 (ar:=7) (rows:=0) (d:=3) ?_) (z1 (ar:=8) (rows:=0) (d:=4) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q294 : block x191 7 53 36=true := by refine (z1 (ar:=8) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q293 : block x191 7 89 48=true := by refine (z1 (ar:=8) (rows:=0) (d:=4) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j134 : block x191 7 0 137=true := (@z10 x191 7 0 89 48 (@z10 x191 7 0 53 36 j85 q294) q293)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j135 : block x191 6 0 19=true := by refine (@z10 x191 6 0 2 17 (z1 (ar:=6) (rows:=0) (d:=0) ?_) (z1 (ar:=7) (rows:=0) (d:=3) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j136 : block x191 5 0 2=true := by refine (z1 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z95 : z28 x191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j136
  · exact j135
  · exact j134
  · exact j133
  · exact j132
  · exact j42
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl191 : Impossible false (z2 1215) 10 (vars 1215).toFinset := z258 (q:=191) (prior:=z8 z57) (z6 z57 z70) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j266 : Lower false (varsX 6847) (z2 6847) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=0) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q131 := z9 z57 11 [(1887,[133,117,101,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j60 : Known false q131 := z5 (m:=6847) z70 j266 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j218 : Lower false (varsX 17087) (z2 17087) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=2) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q35 := z9 q131 11 [(17087,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q272 : Known false q35 := z5 (m:=17087) j60 j218 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j271 : Lower false (varsX 2239) (z2 2239) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=3) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q136 := z9 q35 11 [(2239,[]),(2399,[133,117,101,33,48]),(2427,[130,114,98,81]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j69 : Known false q136 := z5 (m:=2239) q272 j271 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j269 : Lower false (varsX 2751) (z2 2751) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=4) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q134 := z9 q136 11 [(2751,[]),(1375,[135,101,50,33,16,64]),(1403,[130,50,81,115,98,65]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j67 : Known false q134 := z5 (m:=2751) j69 j269 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j274 : Lower false (varsX 1727) (z2 1727) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=5) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q139 := z9 q134 11 [(1727,[]),(2367,[135,50,65]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j72 : Known false q139 := z5 (m:=1727) j67 j274 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j212 : Lower false (varsX 42687) (z2 42687) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=6) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q32 := z9 q139 11 [(42687,[]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(69499,[128,64,116,81,96,49,32]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q269 : Known false q32 := z5 (m:=42687) j72 j212 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j201 : Lower false (varsX 58559) (z2 58559) 11 :=
  z16 (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=7) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def q26 := z9 q32 11 [(58559,[]),(48507,[128,64,116,81,96,49,32]),(43453,[129,82,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q262 : Known false q26 := z5 (m:=58559) q269 j201 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j207 : Lower false (varsX 44223) (z2 44223) 11 :=
  z16 (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (z26 (g:=x191) (i:=9) rfl rfl (z6 z57 z70) z133 z95 (by decide +kernel))
def z45 := z9 q26 11 [(44223,[]),(42875,[130,50,81,115,98,65]),(60283,[128,80,81,67,96,113,32]),(48110,[50,117,131,49,32,65,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z94 : Known false z45 := z5 (m:=44223) q262 j207 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl255 : Impossible false (z2 1279) 11 (vars 1279).toFinset := z258 (q:=255) (prior:=z8 z45) (z6 z45 z94) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j217 : Lower false (varsX 17151) (z2 17151) 12 :=
  z16 (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (z53 (prior:=z8 z45) (z6 z45 z94) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def q34 := z9 z45 12 [(17151,[]),(2045,[48,129,82]),(8190,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q271 : Known false q34 := z5 (m:=17151) z94 j217 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j268 : Lower false (varsX 2815) (z2 2815) 12 :=
  z16 (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (z53 (prior:=z8 z45) (z6 z45 z94) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def q133 := z9 q34 12 [(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j66 : Known false q133 := z5 (m:=2815) q271 j268 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j273 : Lower false (varsX 1791) (z2 1791) 12 :=
  z16 (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (z53 (prior:=z8 z45) (z6 z45 z94) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def q138 := z9 q133 12 [(1791,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j71 : Known false q138 := z5 (m:=1791) j66 j273 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j200 : Lower false (varsX 58623) (z2 58623) 12 :=
  z16 (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (z53 (prior:=z8 z45) (z6 z45 z94) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def q25 := z9 q138 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48]),(49662,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q261 : Known false q25 := z5 (m:=58623) j71 j200 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j206 : Lower false (varsX 44287) (z2 44287) 12 :=
  z16 (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (z53 (prior:=z8 z45) (z6 z45 z94) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def q29 := z9 q25 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(52991,[32,67,117])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q265 : Known false q29 := z5 (m:=44287) q261 j206 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j211 : Lower false (varsX 42751) (z2 42751) 12 :=
  z16 (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (z53 (prior:=z8 z45) (z6 z45 z94) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def z248 := z9 q29 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64]),(45051,[81,130,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q268 : Known false z248 := z5 (m:=42751) q265 j211 (by decide +kernel)
def j182 (i : Nat) : Nat := 0x1ff
def j170 : Packing := (1,0,9,0,0,0,0,j182)
def j176 (i : Nat) : Nat := 0x4a80004900000000000000e0400000c28000000000000000011a000000000000000000000072bcebc01881144a0000000000024cb3b001c6e1c80000000000000000000002a9c0806305e82000000005b800000000000f4a001c9e8900000000705001e48000000000036472b000000006a42060000004040020600000
def j183 (i : Nat) : Nat := 0x150500b00416000c0d8220d0320c02e0b0008058150500b000133024088200781c068180580090000a0240801ca0300a0200601002001eef2270a089600ffd30ffc30ffd20ffc20ffd10ffc10
def j171 : Packing := (6,1,9,0,0,9,0,j183)
def j177 (i : Nat) : Nat := (if i<1 then 0x70000000509400000000000000000e77bdcf0000524b0204d0363c00000000000000000000000000000000000000000000000000000003e9b000144e000000000000000000e9172140008575c2300000000000000000000022a400000014da00000000000000b01c00057380005060000000000000000000000429b00441aa098000048000000000000000000000000000000000000000000000000000000003c1c51ac0009250000000000000000000000000000000000000006274000320000000000000000000000000000000000002d26000000000000000000000796800000000000000000a26000000000000000000000000000000000000000000000000000000000000000219600000000001821000000000000000000000000000000000000000000000000000000000000000000000050b1c0fe00ac95000000000000000000000000120800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003027000081e00000000000000000000000000001204088000000077900003b440000003169e0340000000000000340600000000000000000000000000000000000000000084380000000000000258e000000000000000003086000000000000000000000000140e00030960000000000000000000000000000000000000000000001448000000000039ab000396791580000000000000000050540000000000000000000000000000000000000000000000000000000304f00000000000000111000000000000001004000000000000000000000000000000000000000000000000000030050000000d620000000000000000000000000000000000000916191dc8000000000000000000000000180321b508254540000000000000000087ac0000000000000000000000000000000075800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000704400000000000000000b690000525c000000000000000000000000000000000000000000000e225edb0002c9300000000000000f1b00000000000000000000000000000000000042200000000000c2a000215800000000000000000000050af0a70000000000000000000000000000000000000000000000000000000000000000002c100000000000000000000000001c99000240b0001dac000000000000000030000000000000000000000c200000000000341217b0000000201900000000000000000000000000000001c69507c0000000000000000070a0000000000000000000000000405000000000080000400000020000000c0100000004000000000000000000000100000004000000000400000000000000002 else 0x707400000000000000000000000000000000000000c0b400000000000000000000000000004870000000000000000008000000e5000000000000000000000000000000001424000101300000000000000000189b00000000000000d494000b42605800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b028000000000000000000001009000000000000000000000000141600000000000000000000000000000000000d48410bd06c000000201)
def j184 (i : Nat) : Nat := 0x20a40b42882c0f02182d0010aa01521542882c0420103c64260f41103c0008040f1e0881f8300640b83b801059106c1d41182e0641cc1680088170010b21446304cd05a0a21642902e00013070882b0510aa1480085809013441642c0440301002b02c1280f01685400237826e82b0510aa140220180803601f02c1280b8260000f3d0b2148170010ac13320746a8d119a324620841802d016000122156a1542801a05c0042d04ce82117a1b45c86a0982d00002c122165a1642a850098242c1281f04206c0c01d02e00220941103d0380680c05902e00240fc0a8120200381000a0ad10060001f8130200380a3c0003f0220380a0120a8f0260380805202803028382500c03c08c0a0010260401f00ea0220180840a8100020382701209940940781181400204c0703e02120440800f8130220380a00004c122a0540980e0200f9604c0880e02812141180003c084901a0240580500001822802880a0781080300408200c00401a02b0600d81182e0000b01f481601702d0b413281602902e0021582660240440800f02d03a0600b00003540440800f0290340940c00002c0f280901102003c0f81681d03405800018b8130220380a026580102a04c070105801026044070145008054030058070080f001000900c0140201602a0760100100000d40680d81183105c0c816000800c01402003004004001c0300500900e01001038700900e01001000500a01201001000580bbf41efcf2176239f5c40dc369231e9866b9f5a6ab3d526a364e725c523e8cd43da020f2a72d35d19f8c846112da155c9de4b32360fe470c3081660a404a81ec0bc847019407801e0003ffb02987ff46530ffe0ca61ffd820c3ffb02187ff54d20ffec0a41ffd31483ffb00907ff4c120ffec4a41ffc89483ffa72907ff0e520ffe8ca41ffd53083ffb02107ff60d10ffec1221ffd52443ffa64887ff60110ffea8221ffd30443ffa40887ff4e510ffe94a21ffc83043ffb04087ff54810bfe8c861ff930482ffb12905ff62420bfe9c8417fd19083ff240885ff4e510bfe94a217fd39042ffa52085bf5a430afebc8217bd49042fba72085fb4a410
def j172 : Packing := (46,2,9,0,0,13,0,j184)
def j178 (i : Nat) : Nat := (if i<1 then 0x828800000000303778367c80c46c3000000003026d80ab0000443fc00000000d78412c4c00000000208000000000000000000218d085b1e25a0000000000001411d10b9c814b014e000000001354000000e06e0721d39800000000000000000462a000020bb800035040e13a60998000248342147b20bea0bb404c0000a55bc80b4824ea11a704ef84700000247b3086e018540fe7070623e0327400008087103c4848781346047eb8680000a8e2c10c000030013c48980380b63499ad1d81e09e00004803c0000887a193d58d7118c160dab6a5405055ad3e044db44a04f9c27e40a5bba3882e0c22d2098206550167515d803300000000000000000809c79311914024ced662c82840000612a000000000000000007110fa49e41de2cd4000000000000000000000502080001550e9441005ad000deb14000018340000000002189a854e8e1bcd41000008550000140e1000033aafece2000050a8000021c31e409000000003c23064e0101ed84c9017d404025892548400006f520000000035e168048470a3d5d49a136084c16a000025621b523801c80000821c000000000000146d20000606080000d06a0000b009800000001e0df77ba83b7dc187e034301e0000000000e7be16baa564c1c50557a4b080000027a0000955ab22aa2eb20000900f430f1a0de000000002a2b4000000000000000000000000000000000000000000e04800001c222000000004a5680000000004958000000000000000025ddb406a0000a2085a1e40001002ac0b1c00eb9d8940dbb1aa0001c0000000020a7980df82ac0000000000002c2c80e5eb0980000281918161000052510d8d5a14a0000329f14037c00db05dfbb5f80f90af79082fbd56105502d5000000000c842407e000000003c048c1529b2a1d3d800000000000000003c2620000270f1118bc6287418d24480001ddece82d14a680000000000020400003c00000c000010000000700100205405000020008018080000000000101400400801008004018060000000000000e000000000020100180a00000400000006020000010060000000800e0081300300c000000070000000000000601000000000020000000040040080200e0100081600a0000000101001800800000000000020020000b0000020080000100a000030000060000080300000401800006000008000000080380000001c0000200200801800004000008040020040f0000180040000500000c018030120040b82c00800002000002004000000300880080700002000804000004010010360000780400201c0000401c01c0380000e02c0000a010000018000080000000b008010008010300080180201000403800002000000040020240280401c0080100000a008038020020000180800000c028000040000000100000c00800 else (if i<2 then 0x5445c9bb4f842008dd768b00000821b0202e2220000285a64225e935000000000000124f200000000000012825f280481550668c41800000000119720000a0b280000ceec00007984691c800000000c282083980196a0490031e0334000020a9d091b856441aa23588005b81a2912c00002028f83b1c11d2028a04ff00708040000000000000000000000607c9a4215cf40000e06ba031c000000000000000000000000010300000282e2000040012bd5c00000000000000002804202f07001c007f4293a14d3064aa318a5d0a575893960d0a928d293fa242c81c7c159206200006114d409a40ad00002845400000000000010424000000000000000008a2901038a3d9812c0000e284c04180000000000000000000000001030d00006033f408a089218ae68af8423d28c7000000000c0f6000000005805c000000002720e8039c2860000000000001c16e000000002930c00012119005ca5c3b403a000060540000248cd205cc027d842b282852c7608388253c468d4c46a91000000001005f000028223e8fdc0c580790000114fc00000000000000001e1791062000000000f71deb90800010236000000000000348dae0f600003dc8c00008d43304670191995e00006212800018098000000000000000000000c27f80002920e00006014800000001a0ed00007845342c40000a0b008205402a671c000000001d4d800000000582e80000688c128a80001c123685700002028d42da0000c05e100240001a878c034800000000000040a16006542568470a075281e9c8bcc8c4676780003456f60fab028194090296a476602da80d8d608d45f627aac1c74259a936c0885015802e900b20000350c800014e5f5078d841900fbcf31a02f405200000000012b08000045734093601dd258ad846000084a8683181174000034b3b8b160101c45dc15aca28f01add557f2413a4cfdc7c00008a25da1b641eaccc2b09a501940001209b00000000349e96311a31200000000120ee000000000000001220000000000000eec1104ae89ac5e900000420a63c540000827e000000000000000000000305b81163a05a305a0000000000000000000000000000000000033760ce0e486245b0000240e400000000603c000000000400b4823400004125c20a8143581d0506e00000000229170104e79400000000000000000481dbc0940000473980000edc8414600005a2e00000000000005845d40da6042000000554edcc0000407f98499428ad06c001870a02518a094a7033d8917a97108b4704978051c0bb8079a7b3511be1e5200005087d0570126ee0b61795303e382bc0000a009511295150215b60479890e4a02c0f4000000000000002de00218000202e40000f0a07809c00012137139aa8da0014d4cb0e6ae3bb1c42f040e3809680003c6600000000 else 0x184ec2e4804540000283800000000060354d9f8000000002136000000000485ff05800000c2ba00000000283f00000000090b300002280c230a606e883dd0020c76900000000108150310506700003298da0af028ec549d09c8406611890015f120c40a4543f300c9d6b9cd7654aba11978272a16c8209800019299c0b300040000054e4b3486018c39bfc594a05364a38913c0001809632770000181320000e00600002c8f40000f012800000001e0b5000038ddbc1d3e94e3140c0161c8370176605f9830300820000a05e9b1b382b4d06df00280002125f49480000585d5c1d60000f06f5051082a240b1345c800000001614cd015da0c80001806c0045200bc0001885c2454800000000000000004a4cbc12f66c5000000003007c0000f08fa85a00000208b0000583fac1e7689fc4598000281b80000344c800000000008500000000000006011000000001425c0000201700483c030a16f7094f8490c1cf20aad0696036104b6068800000000000e8905c109aa14212ab264f3000000001a64aa16770113a4c0000002bf00004996808a3e0d1f07d9901702e136c57ab10013ae8dec073182f9a8870113845f206a000032dce0054c8b353900c0d70158144ef84f2401460c274a480002c9ede02ce4a78000385fa0000027b831c2c2ae40fd000021d61083ae945e3372057d41a6000052259947380ef004600005042c9d0cec85a00000000dd3600cc0000300fc02512ccc378600003ce8800003000c34340000a16a00000000280e0000000002044f8832809c6725a853852811670c011d02b80001a06f0000704bc0001492d000000000c1400000b072800024205607591384230e803))
def j185 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x3ff9314c120ffe62930483ff88a4c120ffe56930483ff85a4c120ffe46930483ff89a4c120eff60589483ff93062520dff4c5894837fd3062520dff481894837fc3a62520dff46989483ff93022520bff4e889482ffd1a22520ffb54939483fdd314e520ffe4c1394837fd894e520dff225394837fd594e520bff56939483fed520e520dff624394837fd590e520dff16439482ffd8a0e520bff56839482ffd1a0e520ffe4c1194837fd8946520dff225194837fd3946520dff0e519482ffd8a46520bff4e919482ffd8a54c20bff469530837fd9a54c20bff4e9810837fd9a60420dff54d890837fd3a62420dff0e9890837fd1a62420dff54d390837fd814e420dff629390837fd5a4e420dff469390837fd5346420dff629190837fd3a46420dff669824437fc9a60910ffb609524437fd9a54910ff74c532443fdd534c110ff74c530443ff9804c110bff62930443fed5248110ffe60120443ff95048110ffe4c120442ffd8a48110bff4e920443ff98548110ffe60d20443ff95348110ffe62920443ff95a48110ffe4e920443ff5514e510ffe481394437fd894e510bff629394437fd854e510dff609394437fd524e510dff605394437fd514e510dff485394437fd804e510dff541394437fd204e510dff629394437fd5a4e510dff4a939443ff5514a510dff625294437fd594a510dff4e529442ffd8a4a510bff56929442ffd3a4a510dff60d294437fd534a510dff605294437fd314a510dff601294437fd504a510dff4c1294437fd8a4a510dff4e929442ffd3a60810dff66982043fed8254810bff4e9520437fd9a54810dff54d390437fd824e410dff549390437fd8a4e410dff569390437fd2a4e410dff20d290437fd534a410dff629290437fd5a4a410dff4e9290427fc9a60530dfb4a5820c36fd825a430dbf549690c36fd815a430dbf4a9690c36fd1a5a430dbf069690c37f581464309ff629190c27fd5a464309ff4a9190c27fc9a54d209ff269814827fc9a4c5209ff669804827fd9a4c120ff654d30483fe9524c120ff64c5304837f93062520b7f5e839482efd6a0e520cff605890837dd534e4209ff629390827fd5a4e4209ff629190827fd3a464209ff269834427fc9a609109ff269524427fc9a4c910ffa54920443ff15148110dfe481394427fd8a4e5109ff629294427fd3a4a5109ff668830435fc835e410d7f609790435fd525e410d7f4e9790435fc3a5e410d7f4a9790437bc8352410def54d490437bd8252410def549490437dc834e410df754d390427fd8a4e410df7609390437dd524e410df7629390437dc8a4e410df7569390437dd2a4e410dfb609290437ed524a4109ff629290427fd5a4a4109ff4e9290437ec834a410dfb54d290437ed8a4a410dfb229290437ed5a4a410dfb4e9290437ec3a4a410 else (if i<2 then 0x99b095a08f508c00873084a080907e0077b071606b10688063b05e20595053c04ef04c6046d041403bb035602e5028c022701fe0199013400f3009a00410000fff549814c3ffd9a60530fff269814c3ffd5246530fff605194c3ffd8946530fff565194c3ffd2946530fff629194c3ffc8a46530fff569194c3ffc5a46530fff4a9194c3ffc2a46530fff214194c3ffc8206530fff548194c3ffd1a60830fff549810c3ffd2a60430fff66953483ffc9a54d20fff54d81483ffd3a60520fff42981483ffd9a60520fff66931483ffc9a4c520fff60980483ffd3160120fff26980483ffd534c120fff60930483ffd524c120fff60530483ffd314c120fff62930483ffd5a4c120fff46930483ffd5362520fff60589483ffd3162520fff60189483ffd3062520fff4e989483ffc3a62520fff46989483ffd3122520fff4c089483ffd534e520fff60939483ffd524e520fff60539483ffd514e520fff4c539483ffd804e520fff4c139483ffd894e520fff22539483ffd594e520fff62939483ffc8a4e520fff56939483ffc5a4e520fff46939483ffd820e520fff54839483ffd810e520fff54439483ffd800e520fff62439483ffd590e520fff54d19483ffd8046520fff4c119483ffd8946520fff4e519483ffd8a46520fff4e919483ffd8a54c20fff46953083ffd5360420fff4e981083ffd9a60d10fff54d82443ffd5a60910fff4e982443ffd1a60910fff42982443ffd9a60910fff26982443ffd8354910fff4e952443ffd0a54910fff66952443ffd854c910fff60532443ffd514c910fff46932443ffd9a4c910fff54d80443ffd5260110fff4c580443ffd5a60110fff4e980443ffd2a60110fff60950443ffd824c110fff54930443ffd814c110fff62930443ffd5a4c110fff4a930443ffd5348110fff62920443ffd5a48110fff4e920443ffd854e510fff60939443ffd524e510fff60539443ffd514e510fff48539443ffd804e510fff54139443ffd204e510fff62539443ffd8a4e510fff56939443ffd2a4e510fff61529443ffd834a510fff54d29443ffd814a510fff54529443ffd314a510fff60129443ffd504a510fff4c129443ffd894a510fff56529443ffd394a510fff62929443ffd5a4a510fff4e929443ffd5360810fff56982043ffd3a60810fff20d52043ffd3a54810dff625194c37fd5946530dff4a5194c2ffd8a46530dff624194c37fd5906530dff4a4194c2ffd8a06530bff568194c2ffd2a06530dff669820c3bfd8260430bff4a9810c37fd9a60430dff609190c37fd5246430dff605190c37fd8a46430dff569190c37fd2a46430bff269534837fd9a60520bff26981482ffc9a4c520ffe60130482ffd8a4c120dff66930482ffd9a4c120ffe54d30483ff9824c120ffe54930483ff9814c120ffe5453048 else 0x302702202901cb80181380f014810502301500001e021282582502300f0109601201a014088076002004125100b003000088480504802180101e044300f02380e8c118116000074110a04604203c3806804805c0340280104181c4403402402e01201821c00c0e2201408410900d009082006071004603c0423804c034028010418003403402601e0101fc00c001e01300900e00008a004c03c0428068048410030007804021c03c02801800301180f0108e01007808700d00a006000f008043804807003000080780401d805c028000228013c0280f010a0100e810400c002201a01008405a01700a00e002005300b00680405a0410030007805836804803030801800040401180f0108e01007807601500a004106001100803c04300a03b805001002804102180002301d2c0280f01080ea01400c001e01601008700a006000100e87e07c00603c03a58281821c81cf815e80f980c4808f805a80317fe47fbb7f567f2d7ee07e9f7e5e7e057dc47d477cfa7c957c787c137bd27b6d7b087aa37a6e79cd7944790f785677cd76fc767375d27591754474f77492742d73c8736f731672e17270723b71fa71a1711870bf705a6ff56f846efb6eae6e6d6e2c6df76daa6d756cf86cb76c466c056bb86b776b1e6add6a846a4f6a1a69b5698c6963692e68f968d068a76872683d67c0678b675666e56680666365f26569651064f3646a642963d0638f62fa62ad626c6243620e618560f060375fea5f9d5f445eaf5e3e5dc15d385cdf5c7a5c215b8c5b575b0a5ad55a7c5a1759a65965593058e358a25855582057eb57c2578d5764572f56fa56955654561f55de55a95568553354fe54c95494546b5436540d539c5343530e52d952b0523351b6513950e050634ff24f8d4f104e9f4e2e4df94da04d3b4ce24c714c0c4bbf4b5a4b254ae44a974a4a4a1549bc4903486247e5475046df465645cd4568451b449e444543e0437b430a4299421c41db416a410540583ff33f823f1d3eac3e173dd63d713d3c3cbf3c423bdd3b603afb3a723a013990395b38c6383d37f0378b371a36e53674363335da3581351c34cf345e341133ac332332e232ad322431b33142310130a830732fde2f792f382ed32e862e392e042dab2d462cd52c642bf32b822b1d2aac2a4729ee297d293028e32896283d27e42797273e26f12698262725c2255d24f82493242e23bd234c22ff22a6224d220021a7214e20f5209c204f1ff61f9d1f441ed31e6e1e151db01d4b1ce61c811c281bcf1b821b1d1ac41a5f19fa1989193018b3184e17dd1790176716de1679161415df15b6156914f81487144613f913c41383133612d11278121311ba11491108109710260fd90f980f7b0f3a0ebd0e580dff0db20d4d0cf40c830c1e0bf50bc00b8b0b560b150ae00a9f0a5e0a1d09dc0)) else (if i<5 then (if i<4 then 0xa8134408e04e04405203833c099e04603f02602902301c0a019e04d381101480f0268120e86c0981340740880a06b3012603a04204c09c05180a00a809101c1cc19e04ce0500480d580e8120e7026702a80ac074080678133015603a08c04013037a049f02504f01e02019d028c03f8158130100de0ce80e7c0ac0906d80802a40706f02b0674818605204a03c04202207839200881c407f02501d02a020189180009203f80e8128150108548427c0a41301fc0980806f4074209e05208c04603838037a04a104d01302701d0960201b4101029282284a81f81203f8150100ce80e9427c0ac0780806e4093207e04e03a09c04033a051d01f02b0240ac1b419c188f81580e0dc0da8120c4606ec09c0740a06d0670623e04603a08c050348122049f0260281a702019c09101cf0140d381180e0d40488127c0906dc0740806780a3604834e044052038338121c1a702301d0241aa028098f8120d380f0148100ce048702dc0941040580a40840706c06b4e00827600012603a04a044052109f0270220281a501c090e84e80981380f0140d2810048841140fc09c0880a0674070244208604213c056038352048122104503f02701e02819d02009118138100d20c080e0ce0487c09069068c074080670243e02032e01401e008111901901408a00f009001004199180180a0ca8450040c78027c05802064c01803063040c00420283002d8182002008318102201a0150080840740f018a004079300d00900b804807002044702103080501e420403402801800040540301101e00ee0103140080f2201a0150080840740f018a004079300a0440780c203c080602101e0401c0340200ec02827400820a01400020401ae0180f8078117008182000075100c08a03c0428040c100003a883603e800040201e80f0108d17d0460650590000ecd02203207482e0a007700102c042981105981941841702145e8168004c0882ec0b40001c9505c1700ea00016c0e4c0b502c0b2072402605805001f0392c2ba0c80f81cc0b4001a06f06204506705c0e605a001103602b82e83100102c04c781182e81a417030816800040401080b00a0058000120271c15815415010402c00400014c0e120a6061025026080541281123101621505280040b0384a0940891710d018609c0020590b2405800302d8518c704cc01600142cc298265412413160580b50ab0b6099704c82086c8bc8680b4144858090125441045e4364340a004842c09e8812811c0e40c02c80b8003c07e06e06207405c001a04a04405303103602e0000ed102502181b81881d017000781281101680c40dc0e02c80b8004c0841b407c06018405c000202013807c0ac701500e07603e4c0704d01f02a202601d80f814100ab02301d02604cb81180f0148124c09c0741380840a2e00605604c0420397 else 0x1c1822c04c0e009081160d61140160260800487c0b41501000601163780b21502500f61540bc1301e0677e0a605c08c0340784481d412b0a805e0980f033b50481c00f019c0e80b704d02c18807958268250224104364340fc0740d042c0ce048c61505b00021b21ac1307f2160624b0a209244243a0990b0000058110408312d85522121d04c07800104816d12502c2056c2902c03d01781742c826870861561480bc0b413070330ab0a10d90d00f02010b2092098312985205807902f04c19c188ec620e007642c10c870c2a03c861541381606740b01e06e062422490b011000043033e09b0a00f2702d85585205807902c19d04c189382682410c0e007805a0ce81604803ca0380240850844132e05d0a609a0590b50ab0b040833a585020c20b00185904c0e10490c2882284a80c82081e81607542a02d82680083c0cee2316166142150604130670244304317a0f02703060983301db0b270018598500e01a019904c19d146946301607600005b42a0480c4920723523402103a03002d23121621502403b611911880981c0121685604f00100085018019c19508240480ec8264a15a1421b41221a813067216081062560050a30a10b60990ad0b30a832833a98d502d0000ec0c0184091855181742ac2a42982780042cc280c00dcac13c0ba16c0003861406006e4504517d0d609c0003f80f00583001250b2e8be0001800ec13a02c19809285934350001000fe05b0160c004942c904901e04e024260990411790d82701d01690d10a90b01201db304c8208bc86c1f80b48688501fc858091643645c0e882642c0486a15a1440b216060813067024450b50a30b30a03f012030033c09a58c98c40e0090942b428c2807003c0c00480cf026962e40b074616024281c00f01d0304098338121d8581f80e818204c19c090f01c0fb81681b8180f80778008071c0b80e40c062c00320820781d60683de06200205831a603703a03018b00302cc82482205b81c0cc816800058880f06281004ec0c80b40e80d80003b0635c08c07811c0001d9400003416c08c981d02502302101e03c8190000cd016046b81281007003b03c04006180005b4c08c09206e07010c05a0640001da60481c01000780ecb02407681c0800c301603c703c06101e040240940782000fc08606a074060274004058133204a0450341a410009807407d102207c04c03e0805c08c01c00807c0906507a06c4200a0003c83c0120361b0070000ab02101e024c0618100c6054440405500806f04080a0293c12c07804605603a048338132209504e0441df01c0201d81d407d286e04a01e02203f8140cf01080e9825001c09811c0a80840781f0674c08c08604603815033c09812204a404403c0ab02101c19e02a04d002002381101580e0d5026048812901100fc09c0740806780) else (if i<6 then 0x24240581d830012118598501818c41fe04c19c09100c00480ce30380670241c098300120339204c0e009019c80c00480ce3038024067183de06605831901ed03302c18c901812681c0c40de0580c781701b800a023c0002c06f20140490268159025018809009902502201e0281c9381180380011a0480ca8120d8807a06c1604202a00034e04c0503d036012250410450190040880a819419c1e81b009178100d40df8130140480d8702406c1424826815208202a04203c054048358392c24826d0200980a8b01203b81180e8220ce0547c08c0706f06702a282604d049202403405404204a0383603a0393101c09a0220280a4154c042813011014132580602904018150158148141203c18c09825c1cb02807d02026102601d60a40c612e03b02205581003e81412c81300ec41342782581102907702402606906a04002380740801f7c038290370330118339807e01f0280ac1b819cc12a0dc03f81100e0480ce781081180607809402206a82740a407026809660a40881d833c0400fa052038112407e0450a807b01d02819c09102602148270220d20d412604804c04301080e03eb80806e02406201f01e0673c0401583701203100f80f033a20200ac1b818807c07819cf02101e0fe0e40d580f026810048813001014c01e813067024240881c00f409833812180e204c19c090805480e0df0108121240ee706a407c0940a01f80809106c4215015033e0380fc042048482052407809901c07c1bca04281204c0de441302602140a02406f300f01220380f8339504409008d02409819cc0708140480ce440706f02b06720158378338e02019f01c1bc980e0500ce30284074090742013204203835901c81a701e02902019d024091005004c80e0480de54090260690242203813204012037940a101c09019c882281204c0480ce540740802406722038140120339102409009819c881080e0480ce40280240671a038140120339101c09019c780b0068040c404011e0c6082044908f08e08dc004028220653846e01011032901100c010018c803a0880c63a14a0b61460b20101e215a01067062550ad05b0ab0590080f10a5008338312a85685185585080407882e80419c1895402c2a0b607503c0ce0c4780003d02203c01d08c22106ea0101e540001101e03200e83701350080f260000f0190230100196804079042642a07a0780b607404444240203ca21321402205b02d03c02620101e490581e01d01690981102010080f250441e90000ec80778220cc07380082f82c781906dc00417c18066024c16420881860b83d20b20001c9c07f06204505d0660580ee000101302209383283100082f02c04c881b81102681601f039340dc0882da0c813037c0b00fa206c10205809890220ee04c03e080521621406b08a07f024303781801683d033 else 0x207a085125078924884cc28c1683c44210a0ea14a0c4823847042224141e221350ad00b0a30590592484b00f0312685282c84c2141d488418807904020dc0ce0c4403a20101e0622100837033831101b819c18864424020460d403c0c4606e067062192490083b01301183d80f033a01b819c18864924020800d403c0c4623803a22181e0262920852110c0f0201684e08a000884206806078f8000c00460760cc5c114180a341709006381905ec16c00520b83681180f81c8331a8c704c19c1f423c22c1fc18d01160fe204103808b07f02404e231813430a03d03301201c158598510441e81980741b80e10c2cc290260f40cc0ca0dc070809d03807606202404081281340510098120201081c8d08d48cd22121c1240780000e00ec08c855b04b01e1420800a746e03c1400ec826824b2150970240672600b0a904408117c0304301e03383ec0001202710b00f3f05102904927e09502c0e80b704c180089782b80342ac2b02281482493f04b00c0b689212c10203d0008171c14a1481180b01e43881e0850244138005e0a30ac0811790b043029841033830a0920980f340b502c1b807819cac2a0c28160ce03c0dc661506140b06e01e067330b30a60983383f829918847a285a8501e819904c1941b80e10c2c13a0700800a68240ec826806006605301e21506e0673a0f50aa05a0000f0338371e85418019c1b88c2c42a1080e60fe0778260d40c0903806006e067251a01181c031012168d422c08c18602e854090e436410434428c638260ce0c40a611e0feb21506704940003b0600653d0ab0aa24a00024a05830032a285a8500e021414d0e021104d0c2ac280e007004c0a682213c826961521b09d0380400620670534122164135b0aa0590a80f0338371a8541841b807819cac2a42a0c00ce0dc5062023615024250ab0a90a0300338371818185419c1b88c68c0e42c0c40760460d08700d4c2aa61506006106706e2b0a10b03b04e03f811834609833a58541801841b819ca0440170000760480c0603b8000490600242a09c0583f82783350b0121e82202c0ec1c0090b45e0780fe0cd01603c048780b07f0600)))
def j173 : Packing := (378,3,9,0,0,16,0,j185)
def j179 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x102400000100102800500400200100d00300100200000001000701200502c02f00c00902000200600000600300100900902400300002a00100000001701700400400000000500000300300100400b00300001200a00a00100200d00700100a00000800300a00200101700200001b00000d00000000d00001f00200b00100200600a00300600a00601500000100000500000500000101100300201000000300000300600a00e01b00100200402702200000000900c00a04100400b00500801200400000000300200200000200100400600c00700300500600200400100300f00500a01200000100405b00600600902100700900000c00200000300300000500000f00000700400100100a01600000000301100000000200900200700800e01200300001502c00000400000000200600c01200a00700601203a00200500400000700600c00301900101201000000401100400f00100000000a00202b00701d00200200601f00700302300200101000600100e00500300704500401400000200000400600300201800600002c00500100c00000000e00500600100000000400000000100600200300700000800000600200201400000100300001201600300100200000300a01e00d00500800300000301400400a00f00103700d00000000000200800801a00200201b00000300c02502400500700702400600000200200100800300100200102900100a00000000000700000000000900100500000600100300100600000c01900102600000a00000402200100000000301a00100c00f00000401d00600000000300600900000200000800300000100000703a00100200100000702d00000400d00000400000500100200600d02600000002000702400300200701200300501c01200800001e00700200001200100100000002900800a00800100100000200000600100803000000500000502800000300500000400500900001100800a00400000600200000000500201500400000800101500d00100900b00400900000000100000000c00d00600500a00400000500402a00100000000001200600300100100900001800b00400100200000400000000000000a00000800002600000900200300101f00000400200000301000100002b01e00400500400a00d00800000100f00100700c00000500000500100000000d00300500203201600f00400600e00001801000000300901300700000901701100500a00000300000000000200800100000001100001100302501400600200000400200500400100002c00500300400300400b00300000000203b00500102a00202801301103500101300300300d00700001202100800a00100b00900600600000100200100100800800100400000600d02006000100001000200900000000000000900300700000300d else 0x88e48026d910b8002760e8f580ea0207500f320dc4c1db7001960660810379d4ec80f7202db47027002ed048c182696462ec200280e8a04e6552598899a046f000f4e45f580d28041090080e0aa5c21038885f0603c0d63622fb098260923e0814119a3baa97063dc260dc1c2080e62269a80f1e41b3b0001f0437212f841bd504c1c214ee450ec124a01fcf200be0874882b90a993610e201a540a1f03a966974602c0013ef804240533a09da023a303b9806e9481cc00de583ecf08714081a0117432d060534207fe008bc9aaf80600a44db1214a814f802b7000318001202cb000006cb64424865b8e001d6604b601d6702d38652aa09f381de3802e464e160a29010b600370456a945c180fea93496456320068807a7817b608460ef7d8546580a0c7726013451d75c810b639aaacd048e38c807514269803cc60948024220068603481555ca488b09ad54f340262f831cdb30b264c74830a827a605bd40a5540979bab0e0340a0b30c032e00da3034d6899ec17f4092720963011aac04b80413656d8a0dd58043a0387a0957e00e550dfc128a082bdc9241420488348d27068099341f22223b2055f16f524633d148c0027040170022300000d707840da7c02d203fa6792a2ed0800007040bc0783a0978121a8039a498fb088df449589385704d88ad5800005043fc0347c0c1d2a3d5003a3060a8449d45cd0dcd5843d9e4d8fc0ff4024d103eccc473410afba8fa4568ee90f0879f80dd901aa0000301bc33aab0000020bb59c9bdbc6bc05edc4e6680588904d315ebe08d7011800000000000020ec4ac68334706aa000028128cd13a0000000000c18b6a43408240cebf915b6d8081f050022d5aa9bb713d4c0045809fd1ccae9386456a080ae400005309e503b5840ec00004829c798f460094c044110f50000100380000000000107eb80b600000000000000000002d1026a17dc46b200000d09cd5b8f4083c666a2684740074408f128f6c000068231e0262000028e37e02ee2028b74f138643fc359d66ad40431825c00000d48fa00003c18aa840300001e03e6c1435022a3013760c12511912423304ef80e2f50ed900efb070004404000000000d0966c08a5056580000715c1a134d4a364027b468a6766dcc12180000867080000258486c4779453b6019d4190194cd97931a4e1281927845c1014e00cbfd66680000a79460f1f4000005bbc0000064e1fc0e100000f085e00867809300000146f800002089eca1fb50577046640999d026b315272229000f0090c4538e60000009b308c7a908b6a0b8642659b49750099407980d571043b501f716f304daa83c64e22c0008fbc007504c00000009264809f683d900700b02300001a00b01800400400200000900100700000500400501800d00000901100000104000e01f0050000000070) else (if i<3 then 0x102bc100d73a1fab19a900724000029b58f002c710c040da80cbc4066ce0048000000000000006ad0700161133ef43cc000000000111003020c00000000028887000000000000003c08b000000000000001a3e5c04e20000180e7701d16051a000000000483b0000000000081d9e8366300f6a0a42a245a8401385a660fe3c8c56807d103080000041393b4d41480694107d53330a6c3364e8028cc885290d5105e56056669e5a53ce606d8a0d04000070051a42b2e4e7582168000000001e004080980843200001804f74120722d3c269cc066e81298832690296000000129080d90293b48a6782682039452769a069f008480433a069c00327c08180211c26590896be9c692431c04660000049a38000080795c0767ea3dda47a30316000014890c0177c2065c450b01f49b9880000002980e84380000702a640906d12a30469302e64058642335c2a3222ec8102b489492123f07b800000000000000700306466269ae00000345a5c029b05aa381b4f491fb246c0000104c4438560927000005cb4fb12500000200a8d90c35b783e0e92a217401a9032a12066850f0000006a00f20edfa9ada00039056262ba3cd18d030da76fc410b0008c302b7c66b174f0300f9500dc321ae00002423b80000000006ea79023671979b01a60063928b380000d481ce01bc000000000708b4a0d029c059045400000e01c00000000007038b80562023f80000605baa0bd740c4da07ba09082854a5e308012472716c083b0088c81c0308c2610de023a90356d227982bb080d7901b9722290917cee499835d3291592edd10db13b98308af00a4650eb1003844548e02144172f048aa054140f56c250000003012280ad2820bb14d6e01484e06382221bb4eb158a0000000005503da9682000000000000000000080c9f0264f83f4749078c26381a6bb163000018121f0024a0479b228180b6c00000006c00000000000000000002702a000000000583d400000089860257eca4f003820000225ddd01648b8e60000280c97825820499ef21601918000000000032f4421500000e78f90030b10c5000000000160dfd84c96917e868582c904000000000000002075341d100000a206a00002c05c6206d808e5c0cd440f51299d00001207a700a300000d935acc658000000000f06b2844a00000000004276e00000c212f42cb807fb52d58a4aa00000000000000000003b42f8424a60e4c416a2800a5039e0000000000000000001cab2cc1b1304c3308c901068000000000f267b22bd0499e500b7e0043405a851b86025ce067b645b5e88339390e4849cedfd41a5003a8969120edc50829d52d33025780dbddc2080000607900000149be03806007ce2126f01f78000000001012d609a8381fa405cca0482809b0836520625c0807c195e427e303dfe else 0x4538e0000084182408d10419000ee009c099d88000000000c858d4667b8a92f90c2000004123d113ba00c000003c04780000701560000142382099ec0083002b800004148b0b7a300974591b803a630543a104498458844fa22c74907c0000000003226a490f642409822b861238096508af903dd20472008ed15ccb02ae2151a002cc8218000005206cc0b7000004937e0000060a9100dbc016c708bfc082518c6a80fe1063a8102258318000097536000000000402027094360ec5ea3a80000000002d339c0410383fd08860000301536891d5080a0000000000000000000a217000004a2aa108e20000000000000000000c891000006030b0b359c076f4102703f9706a400000000018a24da4dd80bff40be20cd5309aa084a4c17d3099b0448000002d15ee001b00000000030019e137df424d6097c41280219be07d1043a0d5bc22c84c089160a7a01f75a1f57060d36d770e3a183f10569fc2a5d80bfc5c845480460e314634d0166f0853805376de90a2ad568ba20b180000000000073960f3a10d475b5b7010856f2dc03180000b06a8c0d0f05cc834d57a107412b8d4c820b530752f0ecf209d9e039210244e44aa2dc692b54907974113b5965b83d3205de485f0851ef8287582be007a2c052c21f9501bcef1b9c0e1d0086305890083c8122e834be7139a00378827993d1101c3840cf0256a029d20112e0756a9a700000c9316404100039782570000000000000000285807e460e76052200000a00f1e0e3c00001915b0000042222008c800000000182de78015603034005a08a7f8ddb2cc7c70673cc20ed93c53bebb09a5e457729e47d1b7808bb2064089bfe824849724443e9c11d1a1774434e20b2880e34046b60570206f6d1c49a4768003de10705090104a6f03eb0823a0116600644013b207e180c1b237b6054ba02bdc225f0186678ea200a6d5bb99337b733f001521e48302e00000180f62c1256b2fb90528612b0419bf9346000000000249bc51c68a029294dba01a100000642de00001824d184269062120d844113c02babb6f38078a081c301a27035782c1902093047bf848f6cbb04194a3c6340479c10c741a99b8995449020fefa8b0e818f2018ce0e7d40601a1d8348b3c0f7a805cb00c49129e000018537502f36a359045a4aa39f90b900000a07c541fbf011e073300000181c87247cd96e20000201d9201cd00001690eb9d7d9b09c0000100b890176700ca921fa000008085232cd00001a04ca8106bbb9e000000000350ef7135a628160000080cb081bed02a06e4aa1921011032038e4127400004a436a012a2127008a6800000000140fffc0a220372f095100dac8144402a80a016e6a2989b9002cef44f2d0ec7825e104b2c03f740e55902f313366205fc0cb2c131424737236c0017f88d3c512941608606d8)) else (if i<6 then (if i<5 then 0xa3536c00001c5313a3563019e00001c19728383544f6566a780cbb040e0000088617d98bbbb409027760551d204101aa0071be0394000000000108bd44e7a819e50092044dbe0111c198a04bb901c76051d823ea9a4c40496422600000782f70000060602048f122bb42730200c880c9b0155d00971058d410a481638b37000000804b00000f099d111ea812d80000652a800cb7808b00000d136a2526d00efc9391211340000281639034470302603d449cfddb8c00001e0c3268050991d222d600002c8a7a8266901c800003807d204240000000002c1f3303e5b001e000000d53804b9667c400003404800000686ad211a2ce69e1106e590e00003420211161000014e9ec00006806d9718a2128a41091a176c037000000c0ba80000a0698631a8402c88165107c7405e0c0ba6a479807d7d2d6bc249a829b305c80000000000000020949e0f34000038328000000000082580001470398e0e26c184d12ab043ec0000240d68000000000e07cd4203b53cf8021bc07721dba48442543f1e0c5c01b1980d650857012dd01178ac7ad062741164019c6d04000579e03d8017c4037e8092eaf1b7c0ca083330480c8416a4cd3b008bd0636007af805da9109904440000094ca00000000000000000006843e605f800000000000000105092125bc54a5411f40931685d44105602613079e0000000003833e205ad10575814700000000004916dc1647805b408a3a9059006649b897286ee0a8c41e619960205ae2222800000836ed07022099d80bce10673b6832011b811bc8453e0051204dfc555a00d1c041000002008d801d300001a028400001817da02ce0007e41649028b00000211958c94103f300001e122369ab4028c17539a913b81b202094b097440fd944cf8000000001e0528000020455000010112b5df4800009048c000000000500f1340d200000000075965a06d5a88e200a7324440000174558000011c08b077ded0b609c02099cb03c6809b84c2e68ca9808ce0000281d38000000000010b98231a00bc000002f1d301d790255a04066e021c18700000326e800003c12b000007009c08933406a700ff2017ce0b6a806da04a300000a0b0714cf703468020a8027fc669d199ac0872e51e8293680000e07c340a0c0000703da6484c205015e60438a1540d980646c1a8000000044a20f09c1e1a49baa075b0002cc0bf5004f30375ae4bec1fe6037014871003e311531bb70500a008705414900000014c8e2542008f80000c3869cd13c90c4cdbb846865412d0c188993480000120e2b80e569376a04a9044fdc86b0047e00000000000011c82f0806be00000ea42000008836c00000000000000b70262122e64cc7a41c000004ca60ddd915387005cea0fc09db0510165043d603f3409ac5b887a02b4ea7d58c990460f0955000100169 else 0xadaca96c17d80000104c74ef8c000048391b024e0000148ca0820000278e135241ebe913e000000000300ce810d13015a000028168d843c00000202fcc87b9299b1082a09168000000000404ca0000240f203416002d06d1e9000e7011dd043f01130ce17ba4cda07a1e464f005b29473000018105911268000000001c0a065046781150000000000c2612813f00000a09e6865680000000000000382079018de0376000024cfa10399e090c00003814facb746006c0000000007806890829a0b02404f0000020440249b40000080b200000e07966a44000000000088acb15371042840013601c5c535322512272e40201913f78297921a860d24280a502327083a40a9d9c6880492a035100b0fe935613931269440e1744ab000008480000003404a224700690d0096a01a7e8121502040903d4d55800000000156ad000000032a0000000002c1678cb5f3376e4ea38c05d0000000001ecbca00d278b94503f340e9400000000000001cec95804d4383157984411ba4068180272030ea82370004084ca638f4608f7808848244236ac20bd1293828373802834893b9117184a780397a46a5d143c007f80913aefa8c4ad7a23300001807df9c8340483018a00000041ad00000805d4000000000303bbc01dde893cc16f8806bf376b2023194adb01287190800000001f8010e000018001900f76838640196c26428192884cd00000000000000382182a2fc0000000004388de487600000c1ab883ba23037ce3f70222891110033f608db48a0800004006a00d14ec9d8243e6076a02bf7924b1007634107a299ec581c02c560267f6f3d817448b7ad06292107e415b7baeca02e4c911d01e930228000016ed59c24f2815f00426691df6dab70a378047060a58524278176b220a12dc0c175b3b91502d2e4165d100a33837017ac030401d57892d4526400448c1990ba91e0845a8948001e0816f00001211cd418d78a7000001acb32916453abc001520000100ce00000000000000350fe080317757c000000000101bfe228b00f13ade280000100b020234c229301b2872fda8fff9214093b976147ec970000003a8b976fa346e311649831900001012144190cc3546016ba083040618000000001c0f6c0000201b14091e0000000003013a0189f8055c00004807e00001cd17908cd61172f0094000021922800000000000000402b80000a019b0071140c4000000000000000482a80000f0253208908158500e2702b95406000005d3756a8f049117c0f3d84b6c1705e70d400007030a000000000000000393900001488fcd0ed280d8907c470d558073e8435248c124ce56cb38000000001e0314000000000326d80000000000000044917a818000004843670928c0473410e282b5601d580f814263003b8802c0c02b00127d81143099e64d5b08af2b97) else (if i<7 then 0xb4e4013180f2903600000000006823f00000000000000604c8726f320a4c00003dcd48445a00003c0d9f13430000000002c89b902a2f40c2206288a4e380c790086000015d7c4835cf02e1d2e740000481420000140f03c0e9482745399ab245800004019e706b600000009a000002029000003921e00000000000000201dfe8b38000000000280bd18017b5242000010533583ea000cd403b0c21ec21f7138e420c3c00001a18bd091a0000000004843ae9699371e800004ac82d088ec110400004026a0051e06554882e000000000000000d08ff01560000160016416100000000000000341be38198a03bc0000000004435a2155fe061601668000000000000028035488990000100402909b3ba880a71f0074041a3893559008a000000000000000000000000819d701e1000bde0939c0f67b990000000000000000046d4073ca658ed992980aa000000000000000104b3002a000000000683a09090000001c00e80000165e0000000000383aec044200000000030482a01e0a32fa0e1b0000000001c114202476022300000e4409c89900000675ce00000000021392602e2a04bbc1556cb7e8084360578011a7816b40558e0f160030b849fd4855c0ef7c266002ab0000104e27c4ab9002f00000001bac6668000000001e00ec0000000008042e000004144882bdd3118000028a3af00a20000000003c868102d00000000000c866b8495000012131c0000202b3ea79400000000000000406c0000000000621d9a00a5e024e016cb5bb6744c000e2008d4000008067780b8f809571051106ef40685462652200444c5e43f00000084a9000000000000004827550150e05b881c1581825b47a00002c59380000000012082c09ac80000901be000020e3800000000002041c00000000050272a8f8806561818c0000020899023d783ab601ae00001481cc0000704dbd2ee7402a80000706a2000000000000001089a00001c13780000d4520424c400000000000001c0be6816ae8011c07dba10d000000000000000a0c7dc14c40056f05fb8033b4e2580000703328444281bb004990024794345805a124480000000003dc4ab844000001c4538815fe225fe690208dbc000038af3d063000000000000000fb77fa91c9d125ea3ec703da005314da99a253c0565c023a423b184490000000000c1bc982ad4057d0056a6cb1e116a30645c0e58d4ba0000000000000001090ea371000002218800000037db152cce28c40caf84064071de879f9118c0278c2683e44d000003837b57721c00f800004a1c3f48190075f41af301d6608ad451bee9e280000400414106c9d9f201f457697a0e6140312815d822f7a04b2e9aac83089155c00002825e80000296fb403231ccd582686097f008b4000062242908b0e0bc7c1da0000000000811f0000032425807 else 0x8030fb35160f1b818130162d48e3e0f7c4003c8108d0139600919116600ed432f024d96c20c421e5907fd8ea97cdc4021875235e00001003e23a9a0162e8086800001010fc39a84f1e8e87e8000000000a09f80000000000000004d3c000000000c072e600ad404500000868aa00ba5419f8000000001e03f741b6ba40100000606b200ec0842700227a3218000062404558f3f6ccd804c98269c727400000c1cdc0af9000a7c04061dbb63354000006e8118a4d1b9962008e0000128db50282201d20ca9008325db55106d0e0f25d1f44a9b5304c0c321601d0b01c890818acaf9515d284628826ca00f501e898048e02a5607c00000113730094a2026042010021000000000024039d892ab024ae07779e0bf3b9fa355224)))
def j186 (i : Nat) : Nat := (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x629190c33fac0ab48c8611ff56d2a464309dfad64d2a69066fd6b269534823fe8d934a9a411ff4ec9a605209bfaf64d262904efd6b2693148337eb593498a411ff56c9a4c5208ffa36cd2609057f99b60930483fe4a9aa4982415fe26d514c120ffa30298a60905fe92b169304823fe55a62c4a41cfe6053062520efb262983129077d9300e989482b7eb5874c4a415fe42c3a625208ffb56c4a72906ded525e8394832fec4af41ca4197f5657a0e520dbd856bd072906eed525a83948337ec4ad41ca419bf5656a0e520cdf8b2b5072906f6d52568394823fe4dab41ca413fe42d1a0e520abfaf61ca329056fd6b0e5194829fec5aa6c48411ff2ad5362420a7fa76c0b121055fd7b0e989082b7eb5874c48415df56c3a62420af7a961d3121057f51b0e989082bee8daa69c8419f754d8a4e4208ffb16ad2721057f51b54d190823fec5a748c8411ff56d3a464208ffa564d3068847fd5b269824423fe9d934c12211ff4ec9a549108ffab64d2648847fd9b62930443fb4a9aa490221fdc5455a481108ff956c12728877e952481394423fe55aa694a211ff56d3a4a510abfa76c12f20875ed8254979042afe9daa4bc82157f62c3a5e410af7b16a9a920857bd3b60949043b9ea9aa4a4821deb6095252410af7b16a92920857bd3b54949042beec5aa69c8215f74ed824e410eebaa6a92720857dd3b549390431fec13149c821df3609524e410afbb16a92720873dd8262939042beead9149c8215f74ac8a4e410eebaa4ad2720867dd8a56939042beec5ab49c821df36092a4e410afbb16952720857dd5b4a939042afebd906948215bf5ac834a410af7a9641a520857ed2b20d29042bfa8d906948215fe42c834a4108ffb5641a520857ed3b60929043bb6a9aa4948215fb62d524a410afda76a92520867ed52629290433f6c12b4948219fb6093a4a4108ffb169d2520847fd5b4e929042bf6ad906948215fb6ac834a410afdb16a9a520857ed5b22929042bf69d91494821ddb54d5a4a410cfdb14ad2520857ed8b569290433f6c5274948215fb62d3a4a410afdab69d2520857ed8b0e929042bf6ad874948211bf2ad815a430a5fb160d2d21854fd7b069690c2b3ead834b48615af52c1a5a430adda560d2d21846fd6b2695348237eb593498a41fd254d524c120fec2a4a8a408845fdab20d790422fe55aa4bc82156f5ec8352410ad7ad641a920847bdab20d49042aeebd9069c8215b75ac834e410af3a9641a720855dd7b22939042b6eb59149c8215d756c8a4e410af3a96452720857cd2b22939042bea8d9149c8215f642c8a4e410abdaf641a520856ed6b20d29042bb6ad906948215eb52c834a410afca3641a520857e90b20d290423f6d5906948214fb62c3a4a410abdaf61d2520856ed6b0e929042bb6ad874948215eb52c3a4a410 else 0x215ff62d314a510affab698a528873fd8160129443bfcc02a094a215ff62d504a510efbaa6982528877dd314c129443bfcc026094a215ff62d304a510affab6982528867fd53629294433fe98b1494a219ff5418a4a510cffa60c52528867fd3b629294433fec527494a219ff5693a4a510affb169d2528857fd5b4e9294433fec2a7494a219ff6053a4a510cffaa29d2528867fd804e9294433fea827494a219ff56d3a4a5109ff956a9b040867fd9b4e9820433fead334c10219ff4e99a60810affb3641aa4087f6d5360952043bf6cdb04a9021bfb6093a548109ffb169d2a40867fd9b4e952043bf6c1334a90219ff4e99a54810ebfaa6c12f20875fd5b60979043afe9db04bc821d7f20d525e410ef7b16a9a920877bd2b54d49043bdea9b04a4821def56d8252410ef7a76c12920877bc8354949043bdec5aa4a4821def4ed5252410affb16a9a720877dd8b54d39043bee95aa69c821df754d824e410efba76c12720867fdab60939043bee41aa49c821ddf54d524e410efdb04a92720857fd8b54939043bee9daa49c8215ff4ed524e410cffb56a92720877dd53629390433fec13149c8219ff5498a4e410cffa56c527208777d52569390433fec52b49c8215ff62d5a4e410efbaa6952720867fd8a4a9390433fead2549c8215ff62d2a4e410affab6952720877dd5b60939043beed5b049c821df762d524e410efbb56a92720877dd8262939043beea93149c821df756d8a4e410efba56c52720877dd5222939043beec12b49c821df76295a4e410efbb16ad2720877dc8b56939043bee95ab49c821df76292a4e410efbab4952720877dd8b4a939043beeada549c8215ff56c834a410affb16a9a520877ed2b54d290433fed5aa694821dfb54d824a410efdab6c12520877ed3b60929043bf641aa494821dfb62d524a410efda76a92520877ed52629290433fea9b14948219ff56d8a4a410cffa76c52520867fc3b62929043bbea9ab494821dfb6095a4a410cffb14ad2520857fd8b569290433fe41ab4948219ff4ed5a4a410cff876ad2520877ed824e929043bf6a9274948219ff6293a4a410cffab49d2520857fd8b4e929042bfeada74948219ff54d3a4a410cffb169d2520867fd5b4e929043bf6c5aa694821dfb6ad534a410efd956a9a520877ed5362929043bf6adb1494821dfb4ed8a4a410efd876c52520877ec8356929043bf6c52b494821dfb62d5a4a410efd916ad2520877ed3b56929043bf61dab494821dfb54d3a4a410efdb149d2520877ed5a4e929043bf6c5a7494821dfb56d3a4a4108ffa564d302984fdd3b568194c39f694b04c0861dbb609525a430adfa36a92d21872fd82605690c2b7e95b02b48615bf56c1a5a430adfa560d2d21857f51b549190c39fac13028c8615fd56d8146430afea56c0a321863fd82) else (if i<3 then 0x2ad2721067fd8b569390833fe8dab49c841df754d1a4e420cffb148d2721067fd5a46939082bfec5a349c8415ff56d1a4e420affb16a9a321077f51b54d190833fed5aa68c8419ff54d8a46420cffa76c52321067fc3b629190833fec52748c8419ff5693a46420affb169d2321057fd5b4e9190833fea9a748c8419ff62d3a46420cffab69d232104ffcab54d82442bfe4dab4c12219ff5699a60910cffa74cd3048867fd1a669824433fe85334c12219ff6689a60910cffab44d3048867fd1a269824433fe85134c12215ff56c9a60910cffaa64d3048857fc9b60d52443fb6a9b04a9221dfb66d8254910efd936c12a48857fc9b4e952443bf6c1334a92219ff4e99a54910cffa14cd2a4887bed8260532443fe6c126299221ff5605314c910ffaaa298a648877dd894c532443beeaca6299221df7669314c9109ff956a9b00884ffcab4c580442bfecdab4c02215ff66d3a60110affb36953008877dd9b54d30443bee4daa698221fd754d524c110dfba5498a60885fdd5b4c530443feca9b0098221efe605804c110ffb262c02608857fd9b629304437eea9b14982219ff66d8a4c1109ffb36c52608867fc9b62930442bfecdab4982215ff66d2a4c110fedaa6a92408877ed9b54920443ff4a930090221ff654d3048110ffd2a498240885ff98b4c1204437f6a931490221bfe5418a48110dff260c5240886ff9804e9204427fec5a7490221fde6155348110ffb306a9a40887fe98354920443ff4c5aa490221ffa4ed5248110ffd336a9240887ff18354520443ff8d5aa290221ffc2ad5148110ffd2a4c5240887ff151629204437fcc52b4902217fe62d5a48110ffd2a49d240887ff1514e9204437fcc5274902217fe62d3a48110bff2b69d240884ffcab60939443fbaa92a29ca21ffa549204e510ffe2a2902728877f920625394437fc903149ca215ff2ad854e510cffb56c12728857fcab60939443bf6c12a49ca215ff62d524e510cffb56a92728857fcab549394439fec13029ca21ddf549514e510efeb02a8a728857fd8b54539443bfaa8a429ca215ff56d214e510e7fb02c02728877f98054139443bf6a92409ca21dfe601204e510eff2a0902728857fd8b48139442bfeada409ca21dfe615204e510eff316902728877f95b48139443bfc903149ca219ff5498a4e510cffaa0c52728867fd20629394433fe95b149ca21dfe4815a4e510cffb14ad2728857fd8b569394433fec52549ca219ff5692a4e510affb16952728857fd5b4a939443bfaa8b1294a21dfd545394a510affb169ca52886ff551629294433feacb1494a219ff4e58a4a510cffa72ad252886ff5514e9294433fec4a7494a219ff5653a4a5109ffab69d2528867fdab60d29443beec1aa694a215ff62d534a510cffb56a9a528877f5814c529443bfaa8a6294a else 0x9483bfcd5a60c4a41dfe2ad3062520bff260903129073fd810e989483bee98074c4a415ff46c3a62520affa161d3129077f930469894833fe9d234c4a419ff0e91a62520affa768d3129057fd9b4c089483ff4a926044a41ff64c53022520bff23698112906fed524e8894837ee98a7444a41bfe4c13a225209ffab69d112904ffd2b4e8894827fe85a7444a41bfd4c51a22520dff2608d112904ffd3b46889482bfe4daa69ca415ff66d524e520fedaa6a92729077ec9b54939482bfe4db029ca41fdb549514e520aff936a8a72904ffcab54539482bfe4da629ca41ff3549314e520ffab0298a72907fd90b4c539483bee4da629ca415ff66d804e520ffb2a698272907fe9524c139482ffc8da609ca41dfb549894e520e7fb02c4a729077dd3162539483bfc983129ca41df74c4894e520affab644a729057fd3b22539482bfe8d9129ca41df74c5594e520dff260ad2729067fd89569394833fe44ab49ca417fb4ac5a4e520affb36a90729077ec9b54839483fb6a92a21ca417fb4ad510e520affb36c00729077ed52624394839fec0b121ca41ddf545590e520affb16ac872906bfd82628394837f6a93141ca41aff6058a0e520cffab2c5072904ffd2b628394827fe85b141ca419ff66d8a0e520dbfb04bd072906dfd815e8394836fea8af41ca41b7f6017a0e520dbfb12bd072906dfd595e83948377ec12d41ca41bbf5496a0e520ddfaa2b5072906efd805a83948377ec4ad41ca41bbf5656a0e520ddf8b6b5072906f7d52568394837f6a92b41ca41bdf5455a0e520cffb12ad072904ffd8b568394827fe95ab41ca413ff42d5a0e520cffb36ad072906fed52468394837fac0a341ca41bfd5451a0e520cffb128d0729067fd59468394827fec5a341ca413ff56d1a0e520affb36c0232904ffdab60119482bfecda608ca41ff654d3046520ffd2a4982329077f89b4c119483bfc983128ca415ff4ec8946520affab69ca329057fd8b0e519482bfead8728ca41bfe4c18a46520cffa72c52329067fc39629194837f6a92748ca419ff6253a46520cff9129d2329067fd594e9194833fe2ca748ca413ff56d3a46520cffb36c52a61067fd9b469530833fec5334a98419ff4699a54c20bfea36a9b02104ffd5b4e9810833fecda74c08419ff4e99a60420e7fb16a9b121057fd1b54d890833fed5aa6c4841cff54d8162420e7fa76c0b121077dd534e9890839fec0a74c48419ff5693a62420affab69d3121073fd810e989082bfe8d874c48419ff4e91a62420cff8748d3121057fd3b46989082bfec5aa69c8415ff46d534e420efbb16a9a721077dd1b54d39083beea9b029c8415ff56d814e420affa76c0a721067fdab60539083beea9b149c8419ff54d8a4e420cffab6c52721067fd1b629390833fec52b49c8415ff62d5a4e420cffb)) else (if i<6 then (if i<5 then 0xf4699a60830e7fb36c1302187bed82549810c27feada54c08619ff66d2a60430e7fb04cd3021867fd2a669810c3b7eadb04b4861dbf46d825a430edfa36a92d21876fdab549690c3b7ea9302b4861dbf5491a5a430edfaa40d2d21877f51b609190c33fed5b048c861dfb6095246430affb16a92321877f51b549190c2bfe8daa48c8619ff6ad5246430e7fb04c0a321857fd5b605190c2bfe95b028c861dfd5498146430efeab6c0a321877f52b605190c39fec13148c8619ff5498a46430cffa56c523218777d52569190c3bfac0ab48c8619ff6295a46430affb16ad2321867fd82569190c33fec0ab48c8619ff4ad5a46430efeb02952321867fd8a4a9190c33fead2548c8615ff62d2a46430affab6952321867fd814a9190c33feada548c8619ff6689a54d20bdfad64d2a6904ffd8b26953482bfe4daa6c0a415ff26d3a60520cffa74cd302904ffd3b269814833fecd13498a417bf5ac9a4c5209ffb164d262904ffd5b269314833fead93498a415ff26d31601209ff95698b009067fc3b66980482bfe4daa6982415ff26d814c120aff93698a609067fc9b62930483bfcc0334982419ff6299a4c120cffab4cd2609067fd1a669304833fec0b34982419ff22d9a4c120cff8b6cd260906ff91a54d30482ffc4daa6982417fe6ad534c120ffb336a9a60907fd89b54d30483ff49930498241bfe469824c120ffb076c1260907f795354930483feca9aa498241ffa609524c120dff234a9260905ff98b54930482ffccdaa498241ffa54d524c120ffd356a9260907fe8ab54930483feca9b0298241efe609814c120ffd2a4c0a60905ff89b60530483feca9aa298241ffc605514c120eff136a8a60905ff89b54530483feca9a6298241ffa549314c120ffe30298a60905ff89b4c530483feccda6298241ff626d314c120ffd2a4c52609077f89b62930483ff4a9114982417fe56c8a4c120bff25645260905ff91b22930483ff4a92b498241ff64c55a4c120dff314ad2609077f89b56930483fec988b4982417fe62c5a4c120bff2562d260905ff91b16930483feca9a3498241ffa5491a4c120dff3148d260906ff88a469304837fcad23498241bfe1691a4c120bff3168d260905ff95b46930483bfc4da3498241ff654c9a4c120ffd2a44d260906ff98a269304837fcad13498241bfe4689a4c120bff3164d260905ff95b26930482ffc8d934982415ff26d53625209ff956a9b12907bf5814c589482bfe4da62c4a413ff2ad3162520ffb2a698312907fe9524c189483dfcc0a60c4a41ff64c53062520eff13698312907fd9300e989482efebd874c4a417bf5ac3a62520bff2161d3129057fd5b4c589482bfe55a62c4a41df74c53062520eff304983129077f9814c189483bfca8a60c4a41dfe4c53062520eff0b6983129077f91b4c18 else 0xb00886ffdab54d80443fbea9aa4c02217ff4ed5260110bffa36a9300887ff90b549804437fed5aa4c02217ff56d3160110bffa5698b00885ffd3b60950443ffc85b04a8221bff6ad8254110ffbb16a9a60887fdd2b54d30443fee8daa698221ff754d824c110fff216c12608877fd9b609304437fed5b0498221ffb609524c110bffb16a9260885ffd1b54930443bfecdaa498221bff6ad524c110f7fb04c0a60885ffd5b60530442ffe95b0298221ff7609314c110ffbaa498a60887ff952601304437fea9314982217ff62d5348110fff216a9a408877fd9b54d204437fed5aa690221ffb62d5248110ffda76a9240887ff953601204437fea9b1490221ffe66d8548110fff356c2a40887ff99b60d20443ffcd5b0690221ffe62d5348110fff336a9a40887ff89b54d20443ffcd5aa690221ffe2ad5348110fff2a6c5240887ff98356920443ffcc2a7490221dff66d854e510bff956c2a728877fd9b609394437fed5b049ca217ff2ad824e510ffdb04a92728877fd9b549394437fed5aa49ca217ff2ad524e510ffeb04a8a72887ff98548139443bfea93129ca21bff5498a4e510effa56c2a728877fdab61539443bfeadb049ca21dff46d824e510effa16c12728877fd8b54939443bfe8daa49ca21dff42d524e510effb56a92728877fd5260539443bfec12a29ca21dff549804e510effb04a82728877fd5262939443bfec2a549ca21dff66d854a510dffb56c2a528877fd9b60d294437fed5b0694a21fdf615534a510ffbb06a9a528877fd9b54d29443bfe4daa694a21bff6ad534a510ffeb06a8a528877fd5362529443bfec1ab294a21dff615394a510dffaa6c5252886ffd83569294437fec2a7494a21dff56d834a510effb56c1a528877fd8b54d29443bfe8daa694a21dff42d534a510effb56a9a528877fcab54d29443bfea9b0294a21dff54d804a510effa62c02528877fd814c129443bfea9b1494a21dff6153a4a510bff956a9b040877fd5366982043bfeadb049c821dff62d524e410effa76a92720877fdab54939043bfea93149c821dff62d534a410effb56a9a520877fd5362929043bfe45ab4948219ff6689a60530cffaa44d302984ffcab549194c33fe94b148ca6177f5ec8506530bdfad642832985fdd3b214194c2ff69590a0ca617fd46c8506530bff216428329857fd9b214194c27fed590a0ca617fe42c8206530affb3641032984ffdab208194c2bfec5ab20ca615ff62d2906530affab6948329867fd59628194c33fe94b140ca619ff66d8a06530defaa4ad0329867fd89568194c33fe94ab40ca613ff62d5a06530dfba76ad0329867fd9b568194c33fec4a540ca619ff5652a065309ffb1695032984ffd5b4a8194c33fecda540ca61dfb56d2960830efda3694b041873fd89469820c3bf694a34c10619f) else (if i<7 then 0xffe55b029ca41ffb549514e520ffeb02a8a729077fd9b54539483bfe4daa29ca41bff6ad514e520bff956a8a72907fdd534c539483ff6a92629ca41ffd605314e520bffab698a72907fdd8b4c539483feeada629ca41ffe605304e520fff2a2982729077fd5362539483bfec0b129ca41dff545894e520effa62c4a72907fed5222539482ffead9129ca41dff548894e520effaa244a729077fc8956539483bfea9ab29ca41dff605594e520effa62aca72907fed5222939483fee989149ca41dff5648a4e520bffab645272905ffd1b229394837fe452b49ca41bff54d5a4e520dffb02ad272906ffd31569394837fe44ab49ca41bff22d5a4e520eff9122d272905ffd8b16939482ffe8d8b49ca41bff2291a4e520ffd916a9072907fed52604394837fed5b021ca41ffb549510e520ffeb02a8872905ffd8b54439483ff695aa21ca41dff66d510e520dffb56a8872907fed5260039482ffeadb001ca41dff545890e520eff8b6c48729077fd8156439483bfea8ab21ca41dff601590e520eff916ac872906ffd52628394837fec0b141ca41bff5458a0e520dffb00c5072906ffd59628394837feadb141ca41bff46d8a0e520dffa16c5072906ffd82568394837fea92b41ca41bff6055a0e520dffaa2ad072906ffd80568394837fec4ab41ca41bff62d5a0e520dffa56ad072906ffd1b568394837fe85ab41ca41bff66d5a0e520effb36a9a329077fc9b54d194837fed5aa68ca41ffe54d3046520fff116982329077fd5362519483bfea9a728ca41dff22d3946520dffaa6c5232906ffd534e9194837fe45a748ca41dff66d5360420dff956a9b021077fd5366981083bfea9a34c4841dff54d814e420effab6c0a721077fd3b60539083bfed5b029c841dff6055a4e420effb16a9a321077fdab54d19083bfea9b148c841fdf54d5a60910eff936ad304886ffd5a4e982442ffeada74c1221ffb4c91a60910dffab48d304886ffd3a46982443bfe4da34c1221bff5690a60910dffa7485304886ffd1a42982442ffecda14c1221dff26d0a60910dffab4cd304886ffd3a66982443bfea9b34c1221dff4c59a60910dffab44d304885ffd5b26982443ff69db04a9221ffb46d8254910ffda16c12a4887fed9b60952443ff64db04a9221ffb6093a54910dffb149d2a48877fc9b4e952443fbea9a14a9221ffb6090a54910dffb14852a4886ffd3a429524437fe8d214a9221ffb6099a54910dffa74cd2a48877fd8366952443bfe98b34a9221dff565814c910effb34c0a64887fed8254532443ffac0aa299221dff625514c910effb34a8a64885ffd8b54532443feec526299221ff7569314c910ffdb048d264887ff55146932443bfec4a3499221dff5651a4c910dffb148d264886ffd5a46932442ffec5a34992217ff56d1a4c910fff216a9 else (if i<8 then 0x5246530dffb56a9232985ffcab549194c3bfea93128ca61dff6058946530effb02aca329877fd814a5194c37fea93148ca61bff6058a46530bffab645232985ffd8b169194c2ffe958b48ca61ffb5482a46530bffab615232985ffd2b214194c2ffead9040ca617ff62d5206530dffb56a90329877fd52624194c3bfe2db120ca61dff0ad8906530eff904ac8329877fd52564194c3bfe45ab20ca61dff0ad5906530eff90a948329877fc8b4a4194c3bfe2da520ca61bff5498a06530dffab6c5032986ffd2b628194c37fe412b40ca61bff5495a06530dffb16ad032986ffd2b568194c37fe42a540ca61bff5492a06530dffb1695032986ffd5b4a8194c3bfea9334c0861dff56d8246430effa36c12321877fdab609190c3bfec5aa48c861dff46d5246430effb56a92321877fd52605190c3bfea93148c861dff6095a46430bffa364d2a6907bfd824e981483dfec0274c0a41bff5693a60520eff9369d302907bfd8242981483bfe9ca14c0a41bff5690a60520dffa7485302906ffd2a429814837fe9d334c0a41dff54d9a60520bffab64d262905ffd3b60980482ffec5aa698241dff465824c120dffab4c1260906ffd1a60930483bfe8caa4982417ff4ed524c120bffa36a9260905ffd5b60530482ffe95b0298241ffe42d814c120effb36c0a60906ffdab60530482ffec5a6298241ffe609804c120fff302c0260907ff931601304837fea9b1498241bff6098a4c120dffaa4c5260906ffd81629304837fe98b1498241dff6059a4c120dffb02cd260906ffc8b66930483ffca9aa498241ffe54d814c120fff304c0a60907ff95260530483ffcadb0298241ffe4ed814c120fff256c0a60907ff99b60530483ffcd5b0298241ffe54d514c120fff304a8a60907ff95254530483ffccdaa298241ffe26d514c120fff356a8a60907ff95262930483ffcc0b1498241ffe5458a4c120fff2a445260907ff95256930483ffcc0ab498241ffe5455a4c120fff3022d260907ff95246930483ffcc093498241dff66d5362520eff936a9b12905ffcab54d89483dfea9b02c4a41eff4ed8162520ffeb0298b129077fd9b4c589483bfe4da62c4a417ff2ad3162520fff2a698312907ff9814c189483ffca8a60c4a41ffe4c53062520bffab61d312905ffd1b0e989483bfea9a62c4a41dff4e93162520effab698b129077fdab4c589483bfe55a62c4a41dff6053062520effa62983129077fd510e989483bfe2d074c4a41dff54d1a62520bffab698912906ffdab4c489482ffeada6044a41ffe5493022520fff2a298112907ff85b4c0894837fea927444a41bff5453a22520dffa629d112906ffd304e8894837feada7444a41bff46d3a22520dffa169d112907fed5354939483ff645aa49ca41ffb549814e520effb36c0a72906ffdab60539482 else 0x84db82ab80e37f837e237d2b7bcb7a6b78a376db75e374837323715b6ffb6e336cd36b0b6a13684b66eb652363c361fb60335ed35d0b5bab5a4b58eb5583528350bb4fc34ecb4d034ba34a43487b471b43b34253415b40633e9b3d3b3bdb3ae3371335b334bb328b319330332e6b2ca32b4329e328832723262b239320fb1f9b1e3b1d431c4b1aeb192317c316631503140b12ab10130f1b0ceb0b8b0a930933083b0673044302e301eb0022ff2afdcafb9af9d2f872f77af682f58af3c2f0c2ef62ee02ebd2ea72e8aae7b2e582e48ae392e29ae1a2e0aadd42dbe2d9b2d71ad4ead38ad0f2cf2acd62cc02caa2c8dac712c412c2b2c0eabf8abd5abb92b9cab802b6a2b542b3e2b1b2b052aef2adfaac9aaad2a972a742a512a3b2a2baa0f29ffa9e329b9a989a97a29572934291128fb28e528c8a8a5a88fa87328502833a8172807a7eb27c1a7aba795a786274fa733271d270da6f7a6e826d8a6c2a6b326a3a6942671265b26452628a60c25f625d325b6a5a0a5842567a558252ea4f824e224c5a4afa499a47d2467244aa42e240b23f523df23c923aca389a36d2350a33aa331a31ba305a2f622e022b0228d2270a25aa23e222ea21221fc21e621d021ad21972181216b21552145a12fa119a0e320cd20bda0a12091a08220522042a026201020009ff11fdb1fc51faf1f929f7c9f669f509f341f111ee79ed19ebb9eac1e961e799e431e2d1e171dfa9de49dc81da51d889d729d5c9d4d1d371d279d181cf51cc51caf1c8c1c761c599c3d1c271c041bf49bd19bb51b9f1b891b799b3c9b269b171ae71ad11abb1aa51a8f1a791a631a399a2a1a0d99ea99ce19b1999b998c19761966994a192d990a98f498d198bb98a598891873185d18471837980797d797c817ab978897791763175397371727970b16e196cb96a89692967616531630160015c99599957015401530951a94f114c794a494819451942813f813e213d293c313861369934d131d12f392ca12a0927d92541231120e11de11b4918b11681138110810e510b5108b905b903890020fd20fa20f858f628f4c8f298f068ef08ec70e9d8e7a8e648e4e8e3f0e290e198df68dc68d968d6d0d438d138d040ce78cd80cbb8cac0c8f8c6c8c498c200be98bda0bb70b870b640b340b1e0af48acb0aa18a780a480a1809f509cb89a20978895c0939090f88ec88d688c08897086d8844081a87f107c787ab0795077f07690753073d072706fd86cd869d866d8644060d85e405ba8591057b0565053b8525850284cc04a284728435840583d583b903960379835d03408324030e02f182ce82a502958272825c82398223820d81f781e181cb81b5819f81898173815d81478131811b80ff00e900d300bd00a70091007b006500488032801c80005ffd2b269814c3bfecdaa48ca61dff26d)))) else (if i<14 then (if i<11 then (if i<10 then 0xaa6ea8a6a7aea516a3b6a11e9fbe9ec69dce9cd69bde9ae699ee98f6979695ce94d6930e9146904e8e868d268c2e8ace89d6894688b686ee858e8496839e823e8146804e7f567e5e7dce7c6e7b0e7a16784e775676c674fe7406730e727e71ee70f66ffe6f6e6ede6e4e6dbe6cc66b66699e690e687e671e65be652e63ce6206603e5e765cae5bb65abe58f65866569e553e5446527e50b64fbe4df64cfe4c064b0e4a16491e4826472e4636453e444642e641ee40f63f2e3dce3c6e3aa638de377e35b6345632f631fe309e2fa62e462ce62b862a8e292e2766259e23d6220e20ae1ee61d1e1bbe1a5e182e15fe149e13a611de107e0eb60cee0b26095e08ce083e07ae071e068e05fe056e047603e602ee018e002dff35fea5fdadfcb5fc25fb95fa9df93df8adf7b5f5edf3bdf1f5f0fdf06def75ee7ded85ec8deb95ea9de9a5e775e5ade3e5e21de0bddfc5decdddd5dcdddbe5db55dac5d9cdd93dd8add7b5d655d48dd2c5d165d005cea5cdadcd1dcc25cb2dca35ca0dc9e5c885c6bdc4f5c32dc235c0d5be3dbdadbd1dbc8dbbfdbb6dba0db8adb7b5b655b55db395b1cdae65ad05aba5aa45a8e5a785a625a45da2fda19d9fd59e0d9c459a7d98b596ed92b58fb58ebd8c2589258625838d81c580657c9578c57695739571cd706d6f756e156cb56b556a5d68fd679d66a5654563e562ed6125602d5f355c9d5b3d5975587d578555555325522d50654f6d4da54c454a7d477d461d44bd435d3f8d3e953d353c3d3add39e5367d351d3425332d31652f9d2e3d2cdd2b1529b5271d24ed238d222d20cd1f6d1cd51a3d18dd16ad147d11e50e7d0cb50a8508bd05bd0325022d00ccff6cfe0cfcacf8dcf714f54cf384f1bceff4eefceccceb6cea0ce8ace74ce3e4e1b4e054def4dd2cd95cd7fcd5ccd1fcd09ccd34cb04ca0cc774c67cc44cc1b4c0bcbf5cbd2cbc34bad4b90cb814b57cb27cb11cae84acbcaaf4a92ca7cca604a29ca1a49f749d449b14994c97849554938c922c90648f048da48cac8b4c898487bc85f4842c826481047e047d0c7adc78447614731470e46f846e246cc46afc693467d4646c630c61445f7c5e1c5bec5a8c585c56fc560454a453445114501c4dec4cf44bfc4a9c48d447dc467c444c42ec41f43e8c3c5c3afc365c34943334316c2fa42d742bac297c27b425ec23bc225c202c1e641c341ad419dc1814164c14ec138c11c410640e340c6c0b0c09ac08b4054c03840153fff3fe93fd33fbd3fa73f8abf6e3f51bf353f18befc3edfbec9beb3bea43e53be30bdf3bdd73dbabdab3d8ebd653d3bbd25bd0fbcf9bcdd3cc73ca43c7abc64bc4ebc323c22bc0cbbe9bbc03b763b603b43bb2dbb113af4bae53ac23a9f3a75ba52ba363a203a03b9e739c439a7b984b95b3938390eb8deb8c8b8b2b8963879b863b else 0xae0316004044500f0084046300f0084080303ee005807800057018cd804c00500b0020620319804601dc00018b002063360100ca04003160040446c02700b002062c0002b8c064c00818b0000400319803c0210220100801e010810060210580100601e0108100601e0108100601e0108100601e0108100780402001a380580101118081805c00c00f0000ae0319f00a023049e0040c78000571f00a04003260000c18010319f00b80060160040c60ae3008c075805c00005700206305723008040034018b00202230184029801057e00015c600ae0040c5800020018cc01e010808c601e0108100701e03e00768058000209808201d0118f000041010808c0805020007b00b80100ee00015c06346017001402c00818c15c6c0281f0127800c00808c15c7e01601700843f010810300380005727008045c00f0090438000571f00a06803260070000400319c07c01e00e90fc803e21f818c03c01d282b40a0059051900a004000f80e4805000f92b00724028010003e0392009803e0501814008001f01c901540ab029813809e5c0902a80b8053020013cce31e098b81080a204f01c05450498084088305482a003a0a70101488802100f0c04601e0108c04602100f0c88801e0108c04601e0108c04602100f0c88801e0108c04601e0108c04601e0108c04602100f0c04601e0108c04601e0108c04601e0108c08004400f0084802300f0084602300f008460230108078602300f0084602300f0084602300f0084643f00f0074603e022007803a400e8078042321f807803a321f829803a01e27ae57ad5faccfabd7aadfa8afa7b7a5efa3bfa1f7a0979f379dd79c779b7f9a1f98bf96f795979437926f91df914f8fef8ef78dff8d6f8cdf8c4f8bbf898f8897879f863f84df837f821f8127802f7f377e3f7cdf7c4f7bbf7b2f7a9f7a0f797f774f75ef748f73ff736f72df724f71bf712f70376fa76f176e876df76d676c076b0f69af684f66ef6527635f6267609f5ed75d0f5baf59e7595757f756ff559f5307513f50474ee74d874bbf49f747c74737456f43a741df40173f1f3e273cc73b673a07390f36df35e7355734c73437326f30a730172eb72d572b272a9729372707246f230f227f20b71eef1e5f1dcf1d3f1caf1c1f19ef182717971707153f14af121711870fbf0f2f0e9f0cd70b7709af091f088f07ff076f060f0447034f0257008efec6fd66fc6efb76fa7ef986f826f72ef566f46ef3def2e6f256f1c6f136f0a6f016ef86ed56ecc6eafee99ee90ee87ee6b6e626e45ee366e2d6e246e14edfeede8eddfedd06dc0eda46d9b6d856d68ed52ed3ced26ed176d016ceb6ce26cdfecd06cc76cb16ca86c98ec7c6c52ec49ec2d6c246c1b6c126c096c006bdd6bc76baaeba1eb7eeb68eb52eb436b2d6b176afaeaeb6ad56ac5eab66) else (if i<12 then 0xd010015c36010184126040057140740400570c12e0400570d8040930200188883a0200194609302001846041020018c60400318907c845820832803c08b0201c07580502060000c00630209c0460ae1700903c0230571380402100ea07815c5020018c540201182b86023057090420c201d018c80400318903c0c900e82b8980541080f180401e020190740400570d804821049810015c541d01000ca3410824c080065200f402806800f0084b21301e48040c403a2b0458000af01db05816c0ae3e0440460c8c0060590320c605f2017981605b031f0000be0631f0220aec0b600015e039301800b203ac0b600015e0393814004c200f80840803c0b01800d3800020018cc01fc0002bb02c0af05b1b02c063c0002bc16c5c0002bb02c0af05b1702380001de05982e0b60579c137816c00306415e0b6301a40d0015c0b6000080063381fc0fc0241809009c202700904056020816c03c014061014c0fa038481ac0800490121011604003f00909812045030818a0bf0298100e04904be04b0260400319a43406801801b416a06235048c6206030a82d4044622481fcc2806305a96023070a0980780480b53085887141205b0188a449030185016a01e2f0001420c406181281840403f02d070c1305782b816a6609005815cc1305a8188c06003300ecc2c0b5298bc0c003b02702bcc2c04f3813810406003318580760b5381a011806603102d4bc1302900a80492160570124f22f060c85a092024057980a40c0016809242c0ae0249c03c05b012012417a590448be43401e90b009209e0be448bc0c003b02702be42c04f3c8681000bf012485a09e0be3807817804e0121241002490b02b80c6505e009009c301f019c017216012140e80bd30b1124048530b013c0483e0660000fa0afc05818cc0bc05d812405a03b011980df80b057e0000c450248078174301602e4046302d808c402302d82e0605b0118b01740e60660000c45a0680ef000c0ec0582bc0c6704681ef017c0cc0000ec0c67c0001f404d80b03182d8c06100a602f0000af05b1b01606900a818b0000400319c03e06c1012406003b0131003e06c100540c201f015100b6099102dc0de0b501590055c07c09b02015c5e03a04c15c0b605a9604407903c007816806c310a80cf808e03d04c814c0905720048072100540d207d057018cb804032829e09380101102ccf805c00e00015c0442e0140c80a7c0060040c60443811c87e01d1e01803a07c05901070386c0201000cbc02c008088d805c00d00f0380ae0589b00b800a0160041620ae36014046042c00818f0380ae3e014080064c00e07015c0b13807680407dc000104b804032f0080c5801011180fb801a01e00015c063301000c980003160040c6660181eb0020222600280580103182b8a07c049e0030020230571b8040 else (if i<13 then 0x802d8609301802d86413014012416c4a0981841a601e05b1403e0b605a8c0f002b01802d4980801181268000b5282540fc02805a900c404901402d4806c05a8804602b02482d4941360482db01006ea051a01601e05a8c0d804905a8d8140b5130258140d105782d816a06205ba181204903602d48c0a05b02d4607d033880c4c0a05a8e8120621019c0c4203eb01c0ce360481884062033880ce062100a815e06f04902d4a80901502d8780a015819c6072037b02416a403930240d8067230200d80671b02004809b015819cac00037824816a460380a00ce3604f01c050067201800c8062033900d807a1019c13780a03d813980e604681a40d007b035034404804e401b80fa063180a009c02d05b101a4c0905b0f81202d05b0c12802402702d8806d01202d4602a00f00c016a402701000600b52503f01402a02702d4a06d01202d4602801682d4601d01682d46094027007416a403481380c006705794118c0805702d8809360481b016a404a302016a305784080c070338f80f4080338c0d80671018380e067182340c006d06882d40c40303b01c0ce04001802d8ac0905a80c016c460381b016a360480c00d80b52019c0c22c01d00a1a10222008808007a180c28000ae181e80440ae18330074030020018cbc05057018c602101182b8606403182b86000057018c6040031880740230570c0b74010318f00a0cf06702b80c60410110125001d05a02b860b3066881520cc020032c80b2058880800b11601403a0b2057018c0820223808c15c2e0100880460ae211100460ae1808c15c202002c4404180f0188602302081886040c000188602203181040c44e01008815c3031008c15c322201000c63201024c0fa0ae201eb00a822a0102b8b805046e0000f8093057180740400318f0000400310c0800631008c08206218074044062057901840ae057818c0c40b7c00e001101e02001e8609303e82b86082a0100780c44000c0780c43601024c0800622500c04483a0200188ac0204981000c4401d01ec15c300001000c4301182b8406201182b8602305708080063160100460210110188a0ae061018c840062c00e000f02101181f47c0280f010004607d29110080063180880c78010311010540200f0188882103e818c603a00f20840c4063281000c62a018089074040031158040930200188883a02001946093020018460400118b00c06803d807700007c0270107006901d01000c63020018c580500e80e80c00630208088e023c0002b87c0201102b8604401182b86023c0002b8780003182b86c0201182b8780502701040c1800057980460ae120780f40230571003a02140f02bc15c5822822c0c004026000074023057128040230570c0460ae10110080063181000c62010032403a0ae220e804404005711804821049810015c541 else 0x1d00700af06898580487605807816a301c007816a3605813c0480af2300004603a0571008007e05a8c0600240310c08002303080e816a503d80c18000b5201c416c0b51f03004607d181f40c62e06502c0c63046502c0c6303081c40c60b6201a40f600b031900f40b61500015e0b6180e815e063181c40de0620319381803b0318c0df80bc0002bc980005b02bc780f01d01e80c6401d82bc4c0e01d808c15e400e808c15e300f81000580af2007c0460401d03012603b0579300004001602bc800001d82bc780000fc0780c44c0040780c4301360000c4301360000c4303781ec12603aa06e02c0c7800401e80f740cc00602c1260633e00007481e0311015e0b6100ec0c4260702bc0760622703004607d1808c07607d1b03603e03b0311003f01e0310c126c0d034d0380c380bc0001911c0c01d818c6040031880800621303404603b0311181c0260310c07501e0310c04c0621602f00008d03481f004807d0276031203a020018c6040031880d204ec05e00015e505782d8481e02002bc6c0d013010016c4607008c04c0b6200e80800b6181c404c0b61b03804c062180980800b6180980c4203481a803c02104a01c8c429035818806002405a18048c090570d81006c0578c0480af1009015e201300900d83a00d00016803b2009804806c1809804806c180c016803b180980c42068809009c3a03b02013602a0578188d80905709802c0003c826c0765815502004c360382b84026604018c609b057080ca066c0440a4806503781840ab029281540520b6180a416c204c816c0aa0b62026416c204c80a00c4382901a41aa021039141a8021020008c807101182bc606c05a880480af140240c4203f80e804c04e220588920b603e6002814062381b80480b6182d404c0b61c03c0c404ea0382d4b80800f82d47407812807c16a405a8188540703e80e80e4067281f416a2036019c403b05a8804c062102d40c42c0801fc093813031b02015d800400a80460ae1c0460260ae01502d4b00f03f818805580a05a9a023c07415502016a5c00807416a3c08a1240c002301d02d4c81101c009816a400fb0200760b52204c0420b51e04c0760b51e04c0c580a60393026c07c055024802a032b0200ce024c09d024e07c01302b8649203e009815c424901f015c3037809016b80aa04940e003803782d4801100982d816a4c0980a815c0b5201c00ca0b51a04c0700b51807b0260b51c04c92402a05702d4a03803282d4681301c02d4781305a8b01603805a8c16806a00f01b0806301502d8642ae03e0200540b52900007006f01502d4a80a01402d46c0a05a8816806a00f01c880620578816806a00f0188806704d81a30100b46039811a0d1037602015c06d05a1c15c063102d00d401e00f90a8b80803880c00500b62d04c16e03060502d8a02b01))) else (if i<16 then (if i<15 then 0x780c40b5180f01160b51c07816a2a0580b416a3038813a8160b52502c0e202405a9005b40b00f02d4803b00f016c16a400f304c0480b5201f80480af1f04c1b60b6030019e46207f382b816c284e823481604f057140fc0c206d01b80a60ae301fc15e06051882d4ba15205900242ca1403002d4f40b41c02b98260b52818815c0b51985883c0b5180ec0c00b5180ec8920d8057100fe0af01d82f8840b01d82d460af031013812f412a0982d40c68037019815c3609020a8000b5200880c403b0571005a8380578c1a406205782b816a500b018815c320001801260af05a9403c03b05a8cc2c0b51185883c0b5180ecc2c0b51813c1040ae03702bca41e05a8809cc13037019815c501d82d4461605a8a82661605a8c09e0ae03502bc806605a880600240310c0c0067029e8c742a5d1a00900c4303e8090520705bc8c642a05301802d40c6891a08580f603805b145b203b0310e40f23481082d80d007c03548540fa0240272c09c01e01d82b8809702d82d46038031014c16c4918c0e00c4024200e00a607d01182d8a0af02701fc048430a008c0c201e05a940fe06303382b88614018112415c4d0a104c0f605321c140c60b50570e07041303d807816a5838014c03c0b5242748260c202d82b8ac0080982b8641305b0894501305a818884a205702d80484049985416a350a02d40c43d0a80780c00b5201880b60b51c85542861401182b8a038057304c16a401c02d415c301d807816a30308090461503518500c00d101200c00c4803200c00760622104c06002403090e0a81303082b86a1601d82d4606003f02d46064031018c602300f02d460d1016812415c402700e88920ae268210160ae05b1101606003e0090807e04a82bc15c4027202c15e0ae2602c09e024057930160b60120f0160af0570c0a60ae1704e41121a90a819c0f807a02702de42c05305731826038046c85816c590d48581a3215033823404802d057240fc00001182b8807e00580ec16a401202bc402202480901b0460981980a604990b035cc02a02980ec09207006b9803c0240290c0920bd0570c0760bd0570c0fc04e01d82f8803b02982f8720802981c009e0b62c8bc07807f029807809e603f814c17c301d814c17c326b01f809c0be2014c15c230481fc0c6390408501a207005b1642804e04101a80c00af3704e41121b05b02340d006a03e485804804e5808c0740ae180e807605305a9010407f0318e82607c01202b88413033485816c403802d8403802701980480ae2c04c1a202d01202b8a038046814c07521605b180a607103e485816c501c01000480b52024c0480b51985807002405a900fe06203002d49a1590b28500c00b52985883c02405a9142c61680980ec16a5318985804c07b01c0090d81303001840700b5281d00700260469858048630a0 else 0x8078e0c90578a42702205748040f901e3485007808d03d80741180b53c85007807b03202300ca0b53c84c0b606603e480603c605a80e804c0632007404c0631c82c04408c06481a240207a00e8079320b0110190074068900826c03a01e480e80c0066900c078b21381100b40c007c900c078e064046010015c401d008c15c302002b8403b60002bc60af60002b8601da0002bc603b0578b8220af0570c0000ae0318c0480af1007c0480af180768000af1808c17c202800ec0460be2010018c203182f85811057018f02d800810981bd0c805f0c9590580200318803b057080480af1604401406360c82b8a02a03301f003e0ae2917815c2c0000b40800b6201000c6220c807c0de0ae2600009c0b61e00007404005b1015e0aec0b018c0de0c2c001c04781605b0f0000af05b0c03e06f0570f0220ae03783080c607a05be05b000901202bc401f03782b8602605b0983204e05b0c09c0b6102bc0df800057026c0e2026c0b2183204e05b0c0800631010016c260c80980800b62306007604005b1007404005b0c05a04005b0d83202602002d8803b02001b460af05b009009c08b03f9815e0b626d822c0fe503fa8c40483062813816c3016c0e016c3016809015e3045807807403803e8090d0a244ec04c1840ae05b181040b605f0c11407f01c0234048504500e807607c0121702581304503080a6040342741140630468084142095012201b407e01182b8809503f01a815e0ae2816c0740240271342808b03d807c0b64210121c14208b02d807e03c040300ec16a200f00b416a3016d02c16a3a0582d40c43a0582d40c43a096044126c1305702d40f4062032240b60640180188801e03d80c016a460980900b6062202bcc2807f0121007601e02d82d480b50310815e0b603e822c0fe5031016c15c3005818815c301100ec15c303028580c4336ed21cc2806003e019c0fa4494285903c61420582b8a062a0582b8740b00f02b8603b024807816a450d1b70c280af03e01f40c006703fa5c2a07d05a8c93a870033a078892540b200011607f00f18c68260b503125824c0b0570e03c80b400112415e06005ad04d0438045904c0fa0242d04c16a2057818b02c61505b02d4c07005a8882607d00f014c16a510d822c04803aa098188d4130570815d2160310c116053057104c080505a8188441305702d8661422481f416a460582d4561590b41c2c6206080f1810c0703188180c2a02400f1c0c401e0570cc62413038018003c4383585481607d05a9094441305a8188940b605985016a400f01b80c43057400010c0b520218044060033014cc280b500f208920ae1104c0c008600f02d4b40b30a200016a0622d85489240b03e82d4b40b209b02c16a450b10e00e20622502d81641303102d4a0ae05ba00016a4c0b016c16a3c0b00ec0b60b52) else (if i<17 then 0x203f818004806720180048067181840d42c0681040c23027008c40af082bc380021600ec0c2401d81900de303201bc403b0308885803b0308c09c07d100980d2200f81a4406603608168160481b00d0301200ec0d0301081b0540003480900d0403481b040710d0040d0024035100d406c100918022012040e21012302440246040815e10570403e1604840d006c130000d00211b045802068c049301210130412402a0318c0cac0703e0e810105700900543031819c07402a201a809202603e100d404901301f0806503e00e805440318098402660408054060027026c80ae0d01e04203b037900ca06c0308c0434091301c05206902a9281204004c81bc809903d8b00c04004c81bc807b036080f60991018408020148100407b036080f7028101a40d8203d8264407b036080818061203c0d4072183440e4200f601c409700fe01c0d44600825c16a303390a80c63029019c03a07c202d40c60970369280206a04b8f02380901301a8881102b6024607800e81a0607b0390805407b0130c04d8001009004c067180880d406c1c0880d406c181a80d82c08e0200ce3049807c0d58082007416a06d0499005406702d81f0844903380740f8405b01ba802301082d40da093201a803a06d049900dc02405b0c16a02605b0f00301100fd01c0ce5c08a07c054026033970140240350c0ff80a102d80f805b03e900fe0260688c05406703e0098802a03381f004c4807c04c082067201c804c0af033930141c09840d8101d840fa1c050404c1057604c408b0e04c15c203601ab026324901a8098306881c85808081a80d8203101a858080809820672150885406703e0f010101101a4489201501dc0d44037d01d05442a0339503e06f015019c80b4068880e4105a01a04068036080d406c102b8168205710a84067215080ce42a1504c84340742481bca07901801880de4a0390a80a4067201e00600620351181442a0338c0e407b10344924203a0344407b036080d807b100a02026081cb0142027041a2103481ac402b05781a8740901301c80d44a0412480e406a201c804806a180ac04c06a1809004606a181380f620360409c0d1101381a22027034440002bc8820691d03c15e04e0339008006e01681b4842103700b40da401201a8449201201a860e0067018815e0218111815e10570415c10570415c105703080fa3c0181380f8302001f0504500e8180601d01d09c28e0b20f08848068068c07a0424d008a744a40b4035024c03e249401840b60b5180e81920df180e81920b51d0d81920b5180e81920b5180e81920b5182300740c905a900740c905a8c07481e05a8c1480c902002d490a4020032416a412080b41920402023403b80005a9300008d05702d4980003202b816a490a80880fa0d100ec80415e0b500f0191521512481940f406490 else (if i<18 then 0xdc380f01f0406e030880fa105a840c2105a864272158114084192580f0198501e0330a03c0b50118c16a07c80f0c16a07c80f0c16a07c80f0e03c0b51018203c280f0180501e030080de0c203d0c15c10570415c10570415c1057070000ae06100980de505703080de305700980de36098416c105b0416c10610416c105b40e040b6082d820b6082d820af082d80480ae180b4044290b014c0d4303140880d4303101a80e2303401c404806a240780d0024033900c081e1024f0000600121016c05304982d4806805b01a8126405b10e00cc301c01b405a066202d8321602981a8602d011080d406621c0c10c0a102001a803c062301a807404e03e90016022160000d00b7182d887008d182180d401d03e900dc09321081848c1301c02d804806e2c85826e103ea8580b6421c01fc15e062228580c00620331182401d22482b880b6033080c40661285816c066182d942c0661b02c0c4066181f40e0203802d403a062057140c0c0b102d420b5082d42c0b03381f4892403100780dc02d202d4206280f0180606703eb02c7816a05818887006e282d4300002702d4644903e80798160672b04e42c0b6029824c0dc603381fc0c63057840fc060029819c80aea0982d816a405b0407010570415c1057040fe0af03018580ce503348580d4838202d420ae081fc0c00530339015c1a0982bc09c0820570188c0ae082b816c0820311015c1057040d402d03320e0808205701b8604f05782b816a40578415e105b0416c103081a80e23031016c0c003b201880482027014c408b05b814c0d04903814c16a0b620b6404807d1816c076202701ec402403d880f603b1019c0f8614181a089226002852070065202d8870205b040a601e102d420b5082d420b5082d420b50886c1160ae03e8090a0ae0804c16c0620571015c05305a8c16c105b0642c06241c01b880b5081800fe0af033900dc438102d420ae0814c0462029808c0d4301801a00c230308404606110078c28290a20e087006a202b82c0001181a0763401c01b816c401181a80c23029808c0d4305b01a8870303081a8407f03e01f46c1301c01b860ae0800c206a10184205301181a860b5081840d4243f01800c64492504e09e80b05702d8048605b04c1207c024809080b6082d820b6082d820b6081fc0c00630298148a06602d8148604f05b02d415c40578701684f06102d804850248344048301681800a43c05a1f840b70298180602404690e0720802982d416c403500ec405301d81a8608d0270804808d101a8076205781c409c060201f00a62609c85007005305782d8c60903e0090603c057818c12e04e035180fe0530300c09c07c101380f8201201f0404e03e080f8053101ff026205b013840b603e01f4661603001f40fe40351078501303002bc0ce4035007804807b201a9070 else 0x60b20f088462490570816e103381f4409300f8a402a0b30a019c0fa500f9854406900f08840dc403701a403c2210309503c06712481f482210330184602304981846023049819c6093124819c606703e8849209303e8c0740c905a8c48206e011824c9800037024c606040f01f0780006482300dc405a8419210308074)))))
def j174 : Packing := (1239,4,9,0,0,16,0,j186)
def j180 (i : Nat) : Nat := (if i<1 then 0xb202cde8f2e929f8067f0354a049381aa8109782292102d216f3241b036a0000000004844381b7ce130014d405940352000000001207ff015968a2a0136e0e812338410cd81da0000783dae0fa010c8a00280000000048331826e2336f0068800006ee868122000000000000061bb60000583220000008d2000000001a0ab70005741980001e05c7ba0800007a369208cc043d805580000c0dd00000000078052000008316404b590ee40c7b3bdb408fc98e4000058284000000000a4d4303056439882a1a0bc500f5e01a5904a000000001483ba00d40000681d0c877c10b580b2d013c000030083c0cb7828c00002822a2eab80001808980000a42bf800144a548288404ff396fa0439842a00d7181f32ebba8311206a5805a0000380bcc0549a2e4a035a00a9c064101d3c080f029280316a35ec014400b62094c8359c0ba00000000000001c0f013201006f80001e0db80000000000001c0a768080807dd037b44100000140cef235ab2a3c8245746548a126c70b801c0000102500000601ad00926000de2669a363209aa53c4042b380ba00aa1006ca0e6c99d9487c000016066680de0000400d2000068063e0f5fca9b0099d03cd82dcd82f80044c49bb8051310e0809ccb3400000202edb466303490e6bf21dcc0d9b0423b41b50b960000082d7124e0829f402880000806500001404ab110960b4792ac0000081e6e02aa219f60fc9003dc049b016a000060403606034349830e98192e0b4a0426403c181752e858000100a1e026fc41bd81c5e4ac4a3e2a8d48815e40dc800004009000000000180840838800012e3c00000000000001485e892af20fdc80ce20450014b00b08015a00000000000007839e00000000100b8c8377eead239b780861a37440dc703560000000008000088040040040200c00000000006000000000060140300002203e0140000000601c000010140ac0081e00a014078020000500080000001800003032030018020000b80080000c000000050020080780300001c0080801200c000580900080c80200002002801000078008020040040180203a0080780501603c0180e0080100400001400c00003026000088090000140300a01c0040701900600c0080800000003000012040110030420100000301a004000070020000080000202400005006000018000080000600100001000800004004058010000001c00a002004018050160640300300601404824002024098000080141a0000520000180600201000802024000000000000000e8030100040580a0020ec008160060100000102c000090000180280b804012004008010040040003901005800803048000070020000080080000202c0081e00e0140000000a0a0138000020000082a00a0340100000000c06818014000000020040040000301200403004 else (if i<2 then 0x4a28f400102c2858943ea04679c3a801fb8b8e28d9d00e0e097aa179c63b28138c06f6a3b18093e83dc00003808768d0c80eea2602811f40d8800012c85ca364e1036937ec023c041d61064ca9760f9e8041e02800231801e383440000380b3e041000016ef4a89e22045e004208d5a0055206728035ccfa80000aca9c0076403af83a8000070a182101e0282a096b001a60af5a3bf484b45ac8210a50aa000004009c000000001c075d82fd90eba02a400000000000006804e00000000084348000168b9c80e4000000000a07700000000000001c03180000a0554a1da00006000800d1800000000513c000004b19a649a0835a0000503608465a834ec0ef00001007b0000000006bbe0c0c5500e30cea002c8c103b23542ef213a9fa065a018500634a3b820f43816ec104383bae674481b1a0c9422968871d038380fd08342e0043496f201241939a09b1806b8261b827ee431b9bbc0000203388084650d720765803a0088502b9a4303212fe10c7808cc0c1c3b920000703e000000000000000000000000000160de221448036c03684050e23b3803d80000203f80000000000001e072c386400000000108668000160e3681c3228bf020a000000000802d782ae4412690a72004d02a6000018420228b281e8a063f90b3e042e10e8c2a7510a0202be811a826080000e03a000018105831f4000000001210d6024ce08e80000c09d0000000006daabe873782f20000183aa0000000000000000010e7780000401f181a744a0000000000619d4f412f007000000c9b6a0b6c042c0000000014ee88000000004822260bfe0268000000001409520206c0246028aa0dfd836c80fc04a940ea911bc6a6f55bc37e0cbc010800260da9920694a99d4015d0265e0ca902bb0417f03a68c5cb228dc4aae5a7220eff3bc7400c63848eee930b9a00c6e815d80eb0000024a4e03deef01083a2610e189c020f3f00d8a08e1a3950101338d2c009eb37820bb8002c0000500c272f200000000068075e09c000006a3dd82439666b80be00000000020f14129000006b3f0e4a20000020985021a8427080dc000070214487c803d300d300000c04c0000000000000100a390380e0520000000007839800000319808d80802e00003043a0000083ea84a9d38680000301208ce77339e00002804580fb900d000003817a00000000000002801800005818800001843ec0fed81e2000000000000000001c0c9f21d202020000150e280168b27300001603f223d240d400001e07e181fa14b21098a001bf23ba000048a6264b0f8003e024981ee0000282c0906638409000e2830fb468a02c740e3bb008005b20300e095f038be63ac128da0f27003e00002018600000000088c99a34f603e3a1f620d9182f7b06d10400849c8812ee07845a7520c65b210a0ac70110a02 else 0x120ac9a28f8084a82eb009da4ab380332905be10498217c005280374499c00940000123b540ec082bf10ec78246000000000000000001b49d782d400000806400006d28966f0d829a000061274000000000800a5027a0000581b200005814000f57841460f6481bb80d2e03086041e02aa2075723cd4068283cae058100ec0000301b84039e83b600004233640324038530d0e014fe007800000083ba1b7c26100001c0b78ba97e058b01f042630220b60e5e8072c022781720018082a26634a041fc0c338147e0e23017e20ebd0067e025c01df2e4cc0258c04ec830ba071f0234e005f3b91e00cfa33000006129800e7400b9a012d804720800000060f1e83360000683c2c26fc02b72873980fa20b8580ca204a0000048b791bb8069ce03ec00001833ee0bd0000140ccd80b0000048101c0c0a83b3e022a10a40000202c400001031cc07f1b3b2a0296822c68fc80000206698151c072000006001f9252205f00133a00a893c500beeab7a3463f828000b640312441720279cc80a822f6839c009be06d4821c00ad081e5c0d7f81af205e602e600004010c00001805c80ed40b98e0b9781f520f89906380278042fa106a8334a8dbb800e6cfba0020c0133827c40891a1bb80d01020500c8603864418582cf20a580000263a00000e0e4c83b840ff8000160f91820800837843608ccb83a5006080001c0cf303f9201e80000a4aa68391609760295e070381ce8047710ca2030601cd442ea437a000070241401650bd6342a800010e2a510decee9c03fd52f2e21b04029e8023008d948f580e528262a8cd18299a062801ea40b718176803ce8a1540a44904c0865a837cce6edb1c52059d005f442d8a3e0a04d5b3fee08f323586087983293242202))
def j187 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x87fdac26d835491087fd8c4ec9a54910fbc582605314c91087fd8c56c9a4c910fbd1814c5804c110ff49535493048110ff498354d5248110ff61835495148110ff613c5495148110ff61526ad5148110ff61522ad5148110bfb14c2ad5148110ff61525458a48110ff612c5455a48110ef71516295a48110ff61525453a48110ff6152545204e51087fd5c2ad824e510a7ecac609524e51087fcac62d524e51087fcac62d204e510a7f8ac62d204e51087fdac56d304a51087fd8c56d3a4a51087fd9c2ad536081095fcbc54d825e410b5bd4c20d525e410b5ed2c20d525e410b5f90c20d525e41095fdbc20d525e410f56d53609525e410d5ed824ed525e41095fd8c4ed525e410c5fcac4ed525e41097bcbc54d8252410b6bd6c20d5252410a7bdac20d5252410f72d536095252410d73d5362d5252410d7ad824ed525241097bd8c4ed525241097dcbc54d824e410b6dd6c20d524e410b79d4c20d524e410f74d53609524e410d75d5362d524e410d7cd824ed524e41097dd8c4ed524e410e3dd536098a4e410e3ed825498a4e410f3cd825498a4e410d6dd525ac8a4e410d75d5256c8a4e410d75d2c56c8a4e410d79d5252c8a4e410d7cd524ac8a4e41097dd5c4ac8a4e410d7cd5c4ac8a4e410d7d55246c8a4e410d7d95242c8a4e41097dcbc6095a4e410f74d825495a4e410b75d8c5495a4e410e3dd826295a4e410e75d526295a4e410b5dd7c22d5a4e410b6dd6c22d5a4e410b7cd2c22d5a4e410b7d51c22d5a4e410b7d90c22d5a4e410d7cd8256d2a4e41097dd8c56d2a4e41097ecbc54d824a410b6ed6c20d524a410b76d5c20d524a410b7ad4c20d524a410b7e51c20d524a410b7e90c20d524a410a7edac20d524a410d76d5362d524a41097ed8c4ed524a410e76d535498a4a410a7ed3c5498a4a410a5fd7c0ed8a4a410a77d5c0ed8a4a410a7bd4c0ed8a4a410a7f51c0ed8a4a410a7f90c0ed8a4a41097edbc6095a4a410a7bd4c20d5a4a410a7ed2c20d5a4a410a7f90c20d5a4a41087fdbc20d5a4a410e76d536095a4a41087fdbc6293a4a410c7ed8256d3a4a41087fd8c56d3a4a410d76dac56c834a410c7ed5c6ac834a41097ecbc54d8a4a410b5ed7c0ed8a4a410b76d5c0ed8a4a410b7ad4c0ed8a4a410b7e51c0ed8a4a410b7e90c0ed8a4a41097ed5c4ec8a4a410b5ed7c20d5a4a410b6ed6c20d5a4a410b76d5c20d5a4a410b7ad4c20d5a4a410b7e51c20d5a4a410b7e90c20d5a4a410a7edac20d5a4a41097edbc20d5a4a410e76d536295a4a410d76d5362d5a4a41097edbc6293a4a410c7ed8a56d3a4a41097ed8c56d3a4a410d3ed5c62c3a4a41097ed8c56c3a4a410d76d8c56c3a4a410c4fd7b5ac9a4c520f3d1814c530625208decbc5497a0e520ad6d5c0ad7a0e520ade51c0ad7a0e52087f51c2ad5362420 else 0xc6fd6b56c9a4c52087fd3c56c9a4c520e7d9300ed9a60120a7f90c0ed9a6012096fd6c26d534c12096fd6c26d314c1209ef96c26d534c120bed96c26d534c120bf595c0ed824c120bf994c0ed824c120bfd11c0ed824c120ff489c54d524c120ff49536ad524c120ff49532ad524c120b3f99c609814c120ff4953549814c120dfc92b54d514c1209ef96c26d514c1209fd93c26d514c120d7d95326d514c120d7f18126d514c12097f98c26d514c120d6f96c26d514c120d7b94c26d514c120d7d93c26d514c120ff4953549314c1209df97c26d314c1209ef96c26d314c120ffc152605314c120bed96c26d314c120dfc9314ac5a4c1209fd93c46c5a4c1209fe92c46c5a4c12097f89c46c5a4c120ff49535491a4c120afe92c1691a4c120ff49535489a4c120d3f58126d316252095fd7c26d3162520afd8ac54d3062520ff49535493062520fbd1814c53062520afd8ac4c5306252087fcac56d316252095fd7c2ad316252087fd5c2ad3162520a7dcac4c53062520f3e9526053062520a7f8ac5453062520f3f1814c53062520f7c9524c53062520f7d1814c53062520b7d95c4c53062520b7d8ac4c53062520b3f98c16d3062520b7e92c16d3062520a7f8ac46d3062520f3d9814c03a62520d6ed525ac3a62520d3f58146c3a62520d7d93046c3a62520d3f98142c3a62520a5fd7c0e91a62520a7f90c0e91a6252087fd9c56d3a22520efd1314c11a2252096fd6c26d534e52096fd6c26d514e52095fd7c26d314e52096fd6c26d314e520b5dd7c26d314e520b6dd6c26d314e520ff4953549304e520f3d5814c5894e520d7d53146c894e520ed6d525457a0e520aded2c5457a0e520e5ed526257a0e520e1fd816257a0e520e57d515657a0e520a5fd8c5657a0e520c5fcbc5657a0e520a6fd9c5496a0e520e6ec9c5496a0e520ee6d525456a0e520aeed2c5456a0e520e6ed526256a0e520e67d515656a0e520a6fd8c5656a0e520aeed2c16d6a0e520e76c9c5495a0e520af6d2c5455a0e520e76d526255a0e52087fd9c62d5a0e520ef65525451a0e520afe52c5451a0e520e3f5816251a0e520e775515651a0e520cf6d5256d1a0e52087fd9c56d1a0e520cfe95242d1a0e520cff15142d1a0e520ff49535493046520a5fd7c0e58a46520a6fd6c1653a46520a7bd4c1653a4652087fd1c2ad5362420b3f51c54d8162420a3fcac54d816242093fd5c4ed8162420e75d535693a62420d1fd815ec3a62420d37d8156c3a62420d3bd8152c3a62420d3f58146c3a62420d3f58c46c3a62420a5fd7c0e91a62420a77d5c0e91a62420a7bd4c0e91a62420b7d51c54d814e420a7f51c54d8a46420a7f51c0ed8a4642087fd8c56d3a464208ff90c2ad536091087fd9c2ad5360910c77d5356c9a60910c7dd534ec9a6091087fd5c4ec9a60910) else (if i<3 then 0xefe5526051a0e520efe5525451a0e520e7f5516251a0e520e7f5815651a0e520e7f5515651a0e520cfed5262d1a0e520c7fd5962d1a0e520c7fd8956d1a0e520b6fd6c26d534652097fcbc54d894652097fd5c4ec894652097fd8c56c3946520a7fd5c2253a46520a7fd8c1653a46520c7fd9b2ad5360420a7fd9c2ad5360420d7dcbc54d814e420c7fcac56d814e420a7fcbc6055a4e42097fcbc54d8a46420a7fc9c5693a60910c7fd9a56c9a60910a7fd5c4689a60910a7fd5c4289a60910c7fd1a56c9a60910c7fd0a56c9a6091097fd1c56c9a6091097fd0c56c9a60910d7ed0b26d8254910d7ed8226d3a54910c7fd8a26d3a5491097fd8c26d3a54910f3ed82565814c910fbe582605514c910ffc51c609314c910ffc582545314c910f7cd82565314c9108ffd2c2ad5360110af7cac54d5260110b7dd2c26d534c1109fdcbc54d824c110f75c9c54d524c110ff4d53609524c110df5d5362d524c1109fdcbc609314c110ff5953549804c110ef5d535498a4c110c7fd5266d8a4c110ff690c54d52481109ff8bc54d8048110ff69535498048110ef6d535498a48110bef96c2ad5348110ff698c54d5248110ff699c54d5248110ff689c54d5248110ff68ac54d5248110bff13c2ad51481109ff8bc54d8a48110ff71835455a481108ffd5c2ad824e510afecac609524e510aff4ac609514e510ff6582549514e51097fd2c2ad854e51097fd5c2ad824e510b7ecac609524e51097fcac62d524e51097fd8c2ad524e510f3ed82549814e510f76d82549514e510b7f8ac615204e510a7fcac5498a4e510a7fcbc5498a4e510a7fcac6152a4e510c7fc9b6ad534a51097fcbc54d894a510c7fdab2ad534a51097fcbc54d804a51097fcbc54d8a4a510a7fcbc6153a4a51097fd9c2ad5360810c7fd9c2ad5360810b7bcbc54d8252410f7cd825498a4e410b7dd8c5498a4e410d7ecbc54d824a410b7ecbc54d824a41097fcbc54d8a4a410a7fd8c0ed5a4a410d7ecac62d534a410d7ed8b2ad534a410b7ed8c2ad534a410d7ecbc54d8a4a410b7ecbc54d8a4a410b7ed5c0ed8a4a410b7ed3c22d5a4a410b7ed8c0ed5a4a410b7ed8c54d3a4a410e7ed536293a4a410d7ed5362d3a4a41087fd5c4ac9a60530cf5d524ed5a06530c7dd894ed5a06530f2ed82549815a43096fd5c4ad815a430c6fcac4ad815a430c6fd522ad815a430d2fd5262c1a5a430d67d5256c1a5a430d67d2c56c1a5a430d6bd5252c1a5a430d6ed524ac1a5a43096fd5c4ac1a5a430d6ed5c4ac1a5a430f3e582549814643097f55c4ad8146430e3ed825498a46430e3f5826055a46430e775526055a4643087fd8c56d2a46430c6fd9a5ac9a54d2087fd3c46c9a54d2097f51c26d536052087fdac26d536052087fd5c4ec9a60520c6fd9a5ac9a4c520c5fd7b56c9a4c520 else 0xc7fd9a56c9a4c5208ffd8c56c9a4c5208ffd3c56c9a4c520c7fd8b56c9a4c520a7fd8c56c9a4c520c7fd5a26d814c12097fd5c26d814c12097fd5c26d314c120a7fc9c4c58a4c120a7fd5c6059a4c120a7fcbc6059a4c120a7fd5c22d9a4c120a7fd1c22d9a4c120a7fd8c16d9a4c1209ff98c26d534c120bfd91c26d534c120bfd95c0ed824c120cff8bc469524c120bfe98c54d524c120f7e9892ad524c120bfe98c2ad524c120bfe91c2ad524c120ffc953549814c120b7f89c56d814c120dfe95226d814c1209ff95c26d814c120dfe92b54d514c120dfd92b54d514c120ff5953549514c120fbf182605514c120b7f98c26d514c120dff18126d514c1209ff98c26d514c120d7f95326d514c120d7f98226d514c120d7f95226d514c120d7f98c26d514c120d7f93c26d514c120ffc953549314c120ffe152605314c120dff18126d314c1209ff98c26d314c1209ff95c26d314c120bfd95c26d314c120bfe91c5488a4c120dfe95256c8a4c120dfe95246c8a4c1209ff95c46c8a4c120ffd1814c45a4c120dfd93162c5a4c120dfe9814ac5a4c120dff18146c5a4c1209ff98c46c5a4c120efe8ac5491a4c120efe9522291a4c120aff95c2291a4c120aff98c1691a4c120abfcac54d8162520d7f58126d316252097fd5c26d3162520cff5812ad31625208ffd5c2ad3162520ffd1814c53062520a7fcac56d316252097fcac56d316252097fd5c2ad3162520f3f5814c53062520f7d5814c53062520d5fd7b5443a62520a7fcac5443a62520d7f55146c3a6252097fd5c46c3a62520ffc9524c53022520bfe92c16d3022520aff9ac16d3022520dfe95246d3022520a7fd9c5493a22520ef6d525453a22520afed2c5453a22520efcd524c53a22520efe9524c13a22520efe9524c11a22520eff1514c11a22520cfed524ed1a2252097fd8c26d534e52097fd5c26d814e520ff6552605514e520d7f58126d514e52097fd8c26d514e520cff5812ad514e5208ffd8c2ad514e520d7f58126d314e52097fd8c26d314e52097fd5c26d314e520ffc552605314e520b7dd8c26d314e520b7dd5c26d314e520f7d5814c5894e520a7fcac544894e520d77d5156c894e520d7dd3156c894e520d7f55146c894e52097fd5c46c894e520f7d5814c5594e520a7fc9c6055a4e520a7fd1c2255a4e52097fdbc2245a4e520afedac22d520e52097fcbc545890e520a7fd9c5498a0e520ebed526058a0e520ef6d525458a0e520afed2c5458a0e520e3fd815658a0e520e77d515658a0e520c7fcbc5658a0e520eded526057a0e520e5fd516257a0e520e5fd815657a0e520e5fc8c5657a0e520eeed525456a0e520eeed526016a0e520aefd5c6016a0e520e6fd515656a0e520e6fd805656a0e520aefd0c16d6a0e520ef6d526055a0e520e77d516255a0e520)) else (if i<6 then (if i<5 then 0x2bb4446862d079a0cb40667e6cf499cab36666a6ccc9988b30c659eca8193fb26c64b2c8e190bb20463e2c7798deb1aa62dac5698a3b1346242c40186fb0b0611ec1b9826b02c6016bfa97ebafc45f62beb17d3af945f02bdb97b4af645ea2bcf978eaefc5dd2bb59761aeb05d3aba2973bae645ca2b8c170eae0a5bd2b7596e1adb05b3ab5f16adad3a5a4eb3a9664acb65946b279645ac8658e6b1b961fac3a5832b0515f9abee57b6af215e1abbe5756ae615bbab6456bead695aaab50567aace1584aaf655e2ab79565aab8554aaa11538aa5e5496a8a9512aa1253fea7b14eca9b8532ea5d94aaa9345242a40146fa8be513aa1f142da83a50329fe13eba7b64f0e9d993a2a7244e229bc1367a6ae4d1a997931ea61c4bf697692dca58a4ab694e928ca4f849929269235a42e47fe8f411d0a348464e8be116ba262448288490f8a1b4432685910a1a10641ca82d904aa05840367fe8ff39fb83f2e7da0f9c9f183dee7b20f539e783c5a7830ef59d763aaa74d0e899cf2396a7250e329c4438466fd0df09bce375a6e30db59b4a36366be8d739ad435666a80d3f9a5e347a6838cef99be333a65f0cad992c321663a8c6498a8310e6198c2298242fea5f50bd997922efe5d78b9e972a2e2e5c10b7196d02d7a5aa8b4496682c725898af495d62b6a5618ab295522a465440a7e94dc29765268a3c9458286e50589fa93e227824e809c6936c26964ca898492e8258e4a989429264248647e08eb91a8230e45988a291242206438886790a020e2414081090001fbe3ef87d58fa61eee3d2078c8eea1d763a3072e8e3c1c3637e86e58daa1b12356869c8d1819ee33206538c8618ca31106118c0217c22f005cf8b7e16ba2cf058d8afa15b22ae054b8a76148e289850289e4138626884b98944124623d046988b21106218842088200ffe1f783de879c0ef61d30395870a0db61ab033e865c0c7618682fc85d80b6e16202b385460a4a141027184a6090a115821383f807ae0ed81c38366068a0c9018182e205820a801388250045e08380f681cc0356062809f80f4013601780108000c7fd9a4ac9a60530c7fc5c4ac9a60530c7fc9b6ad52465308ffd8c2ad524653097fcbc5498946530cfedac4ac8506530a7fdac2095906530e3fc8c5658a06530c7fcbc5658a06530a7fd5c4a58a06530c7fcbc4a58a06530af7d5c2095a065308ffdbc2095a06530af7d8c5495a06530e77d526255a06530c7fd2962d5a06530adfd7c2152a06530aefd6c2152a06530afdd3c2152a06530afed2c2152a06530aff51c2152a06530aff90c2152a06530a7fd9c2152a065308ffdbc2152a06530a7fd8c5652a06530c7fcbc5652a06530c7fd5962d2a06530c7fd8956d2a065308ffd8c56d2a06530c7fd9a46c9a54d2097fd5c26d3a605208ffd5c4ec9a60520 else 0x8200b602b860300048201380ae10048827880be0812605f08093018c4057040ae0815c102b80b61015c102bc205b040ae018c400b0136202b800b02d460798407f018006302d4805784030019c407d806007d0c03b03d4405b0404e03200231f0001018c206d015e2024c0af101600578809302bc4049815e203e40af101f0057880f703d8405b0407102d84027016c202d82000816a201bc0721004c01d8807b00ec400e80c620208063100f60788a02901bc406881ea2007c0b51109203f8054031816a543d002a100ce03e01e6300900631015c0318a01303cc405a816c202b80b511022031880b5080ca031816a3018c02a02d4606881e2201e406700ec607901e2200ec0b51001605a8806108002140880e81803d06801c8303c009703986023012e0730c0a902080cb1812600e81963e0140ae032c603201cc200740ef1003a0658804283400e2181dc0570809702b85c02815c0318c042018c4032015c200040ed1004301101d03025c0be1012e057080ae018c404980c6201900ae100000570807a0188403d015c2018c0ae1012e05f08082018c404100c62025c0ae1012e05708082018c404100c620208063101040318802180880e81815c03188093018c403180c4201f4063101d8065888c503ac0ea1904207200c6303900631104207200c6301900ae1000203e0802180880e81812e05f08082018c404b815c2025c0ae1012e0570809702b8404980c6200000651700a05700c6301900ae101d20578881e03900ae19160072815c320780e402b86072015c200000ae1012e0570809702b8404100c6202080631700a05700c63007c07a1002a0570800101f0404100c620208063101c8010803c074100e70398440f01c80570c8b003940ae1903c072015c303900ae1003a031880e302080cb1812e05f08082018c404b815c20208063101040318809702b8404100c62e0140ae018c604980c6200e8065100c80570800101f0500e81c4201f00e2100f80710808a03080bf02f404029070037015c05780c4500a80d702b80b701440bd3004802d809205e90024016c04902f4801d8046287d70f9a1f0c3c0873f0dfa1b5c35886a70cca196c31a860f0bd2169c2b2852309c2127c22e841b07b20e5c1aa831306120b1c1428243043a076c0cc8157022a02dc02c8016ffa9fe4bfa87ef2fd61fa9bf327e3efbf9f6ebeca7d36fa21f3abe707cbaf929f14be087bb2f6e1ed2bd847aaaf499e82bcc8794ef251e39bc527862f079dfebbdc775aee31daebb3c7636ec21d6cbab8752ee9d9d31ba427442e839cf6b9da738ee629cbbb956726ae419c79b8c4712ae199c29b8327006dea9bc4b75a6e8edd09b97b71c6df6db69b63b6a66d26da01b2fb64c6c72d861b02b5f26ba2d6c1ac7b57c6ab6d4e9a85b4ea69aed311a58b49e6916d1e1a) else (if i<7 then 0x4200ae1815e085015c084008405a980ae02d4405b016a0318c06308004e080e21034402d1640e03188097080c60120807d0e4621018802410048158c4207a81a2201942227840f501ec405a81182014c06a1089e1030807b102120688a01302d80651816c0410808208070103d420308406408212103d40d111026101b82e09840079840f3081a20168ac1302d807a0090990400c605b0c0930816c0120808202d840b04c0ae014c0d72015c084016c303080d7101f8103cc2079815e2019805b10048141f82079840ae018c40578641302b806300908079840ae08048100e8205b0048203080b6101e605b00c6302d804e1009c0278804e0344402701a220344030100f601808061081e2103c420001f0103c436048400b0243604840d101c4406880e2200982078840f1081e2101bc20578403b0813a101bc200f80d42041c200f8406d0078403f840670812610078203180ce2019c03a101a205b880ae0820c07c020a03390063019c4033840f108002a0800f108010603c40ae1800d1007c4002d00691000f20b8121001c07080de101e406f10168100000d01c201314105019c7a03840074040e4081d010188204980c6203902074040e80805a030080071040e2081c8103a0207200c620308063101840300806800745c0280c627008204100c62c84c063100fa0118b81102f8406f020820378103101dc05f080c602f84041018c203b80be101dc0570802100980be1812e05f080c602f8404d815c2e0003c08815c201bc0af100de0318801601f0405b02060108c03a0188400a816c201380b61003a0318810203fc404501040798c08a02fc0f31803a0318803b02d4400b016a202f00240388604589900790c0af01fc02418116057816c03f9002200ec0ae1820201d815c3008803b02b86045815e05b00f803e80fe602d4063100ce03e88923b0480b51203c224811603fac63a09816a031a301101f0423f00a605a8c0b501884057804c00f01164c04541316826049815e3c04402616826029a0e00801301100985a09815c0310c4490398423f01160570048402bc06302b80b62015c07f880b50810c05a80c4380780b5100cc058004c3112640b0188605b816a2022c0b510104027815c303300e6100fe030016a301fc0af018c06002d4a05b016a201000b51015c031815e05b016a0310080011a00cc0398402000c6202080b51015c05a880b002bc0ae00988031015e202bc06202d4605780c4202d40621015c033016a302d4205a8401602d44037015e201380ae100dc0578806001980b518104057880af0815e10004061100c4101fc44f108fc05a880fe0398405701fa2278c0ae02d804018080227880ae01884609815c201840241005405701ae302f40e6101980730808202bc402981ae203040e6101f80730802d02f84064817c2c else 0x42407b100003d8126201ec0b710192030080e2080dc1001a2032080030840e2080c41023007d101ea068880ec02d44064816a203cc0b51019205a880c902d4407980dc2007406e10126030080d100744003900d110192068880d1024c56098409b0190402981a2203cc0d1100a60688807c014c07d1811406101a23e04b813100c80370807c024c404980f62132008201f4607a81a22001a2018080f2080f60180804e01a8403e840af018003b181e4101f42001fc205a840b5018c405b00cc2022c0b5014c604580a6200e8203e00742022c07c01f46057016a05b0c0af0098405a80c4012089e401a80531003c104241011011700f0b413c04440848407d02d4405700c4202b8082113c604100d4202b807d014c605700fa20180093100f8198c6070019c6029809c202d40621010c05a880b50815e031080530198405b8406701c44038840b70e826083015c05a9004f081e6031880660208405a80a603e0c0620816c05700c4302bc0ae02d46057816a0318c066080c4033080af0)))
def j175 : Packing := (544,5,9,0,0,15,0,j187)
def j181 (i : Nat) : Nat := 0x341e500f10b5023019000000000000000000000e039d99a054c0df04e010a1200003000000f06000000020060003de33089802a6940000000000878800000000008082c01124290c00025060001409e26e405c0759a4744400023788230468000511c25100024cc0000000000000010978110002e17807f6520003c0a8421882e0700000000000000189f0002c045051886244c000f06e4dc0000000309309d24434da0002021201dc0f0003c1200024c2405980be05d1e10000c0c000001a162000000000000000180000400300040050000280000c180061c001
def j259 (i : Nat) : Nat := 0x7d080045840458400682602d84014c3c04420016a1000630806608066080b600c4018c6018c2041c200000318405780b6100530200202001004c100fe02d44018805a8805a8062100b500c42015c02d4402d42007420002c6b06adaa294a027b9da538fe2b89a12835f9795d167d8b5dd725b56855131438fa398c32807d1683708c0f028050030dfad6c62b64d26290497f5f49c4c58a4c120bfa48e938a9aa498241f74953624ab549304837e92a68e156a9260904dfa2751c2ad524c120e9f8c13024daa29824196f98c5b09b54530483af6302a6136a8a609065ee6314c26d514c120ebe8c0a784daa29824197d98c4f09b54530483bf830298a562d2609065fc6049c46c5a4c120c9fac0ab84da62c4a41afd1812b1314c1894834fab0256262983129041ff2b55c46c3a62520f7e0a92629823444a415f68bd54d5260120442fcd2da562a6a9240886fd85493c2ad5148110b7b256b04a92a29ca21e3658254981569190c2fc92da4e2a6a92609065ae5b14c26d514c120cbcca62784daa29824113f98d2711b16930482de915aa9aa498312907cf0549814c53062520d9e8c0ab898a60c4a4127d8ad571314c18948367a30256262983129074f46053046c3a62520e7b0a92a285a341ca41bf2152530ab54520443c69aa6c12a4c52720878d3609526295a4e410
def j254 : Packing := (38,6,9,0,0,10,0,j259)
def j257 (i : Nat) : Nat := 0x12100000000000340e920018094000000000000003a10000000400
def j260 (i : Nat) : Nat := 0x2d802d4400005a8031880188018c5527ca4a0396b1815b14c26d514c120e4f46058c4f09b545304839791815313c26d514c120ecd054981571314c18948323d1812b55c4c53062520
def j255 : Packing := (5,7,9,0,0,7,0,j260)
def j258 (i : Nat) : Nat := 0x34000000000000000
def j261 (i : Nat) : Nat := 0x1c8d0549812b55c4c53062520
def j256 : Packing := (1,8,9,0,0,0,0,j261)
def xmsamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc93c600104800f00033a821010a4040000e784c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x2a2c892948494384049443e911490019504944c10118c800b1801080946484481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03000c538c42003890004200000001bf8e7a10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x1092049602b0045b1b60a410c4864fe48810a10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x26010014d0082046000004200913f9d3b00800001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0xd485220dd0e2184e48942ed2940800050c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0x30030208803b402c44c001474203e88004100600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x20332dc802e0524012408c02d4a45a41ad0a460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0xe420804100c080000035552a400000400380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x15c05216b516ac3be92b30142a12a5a602b4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0x9803c2203009310323fc888000806200200400f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x58336c48484301962402c12a02457c025168000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x4081c02844008188003000a440000c49003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x2d293b48ac4cfaa06402188b33303003372f56a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x6000c1040009050300540080910116000083ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x3234891b2271ce6219369100569b283f8a287ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0x10c09122032340a044c03882a448020403107fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x1244c0335113050689bd4364084b803c40c0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xmcolumns : List z35 := [(1,0,510,0,12),(2,0,509,0,12),(1184,0,1375,0,11),(1156,0,1403,0,11),(69122,0,69629,0,12),(59906,0,60413,0,12),(52753,0,53230,0,11),(42752,0,42751,0,12),(42504,0,42999,0,12),(42528,0,42975,0,12),(42628,0,42875,0,11),(4,0,507,0,12),(1538,0,2045,0,12),(1792,0,1791,0,12),(1696,0,1887,0,11),(69137,0,69614,0,11),(59921,0,60398,0,11),(49153,0,49662,0,12),(48260,0,48507,0,11),(43010,0,43517,0,12),(32,0,479,0,12),(256,0,255,0,12),(8,0,503,0,12),(2180,0,2427,0,11),(2208,0,2399,0,11),(2368,0,2239,0,11),(69128,0,69623,0,12),(47624,0,48119,0,12),(17,0,494,0,11),(134,0,377,0,8),(9,16,486,0,8),(3,0,508,0,9),(1188,0,1371,0,8),(258,64,189,0,8),(55305,16,55782,0,8),(289,0,222,0,7),(7,0,504,0,7),(47633,0,48110,0,11),(35,0,476,0,7),(44546,0,45053,0,12),(42652,0,42851,0,7),(52819,0,53164,0,7),(42532,128,42843,0,8),(42760,0,42743,0,9),(1794,64,1725,0,8),(264,0,247,0,9),(27656,0,28151,0,12),(44568,0,45031,0,11),(288,0,223,0,9),(58624,0,58623,0,12),(17152,0,17151,0,12),(52992,0,52991,0,12),(47872,0,47871,0,12),(44800,0,44799,0,12),(27665,0,28142,0,11),(46112,0,46559,0,12),(43330,0,43197,0,8),(2306,64,2237,0,8),(33,0,478,0,9),(268,0,243,0,7),(69129,16,69606,0,8),(12297,16,12774,0,8),(69254,0,69497,0,8),(1288,0,1271,0,9),(14,0,497,0,7),(58690,0,58557,0,8),(8,16,486,1,9),(55304,16,55782,1,9),(1060,128,1371,0,8),(60038,0,60281,0,8),(18566,0,18809,0,8),(177,0,334,0,7),(46080,128,46427,36,10),(36,128,347,0,8),(0,128,347,36,10),(18593,0,18782,0,8),(69148,0,69603,0,8),(59987,0,60332,0,7),(296,0,215,0,7),(43266,64,43197,0,8),(344,0,167,0,7),(156,0,355,0,7),(46116,128,46427,0,8),(21,0,490,0,7),(17154,64,17085,0,8),(52994,64,52925,0,8),(44802,64,44733,0,8),(12305,0,12782,0,11),(2240,0,2367,0,11),(83,0,428,0,7),(12288,64,12477,258,10),(28,0,483,0,8),(58368,64,58557,258,10),(12546,64,12477,0,8),(2212,0,2395,0,8),(7681,0,8190,0,12),(24,4,353,130,6),(256,8,227,20,7),(260,8,227,16,6),(257,32,94,128,6),(258,0,189,0,8),(18,4,353,136,6),(136,256,23,96,6),(96,1,396,18,6),(64,4,305,138,7),(16,2,424,69,7),(64,1,396,50,7),(59911,0,60408,0,7),(42764,0,42739,0,7),(129,2,312,68,6),(130,1,332,48,6),(132,2,312,65,6),(49161,16,49638,0,8),(260,0,251,0,8),(42792,0,42711,0,7),(42520,4,353,130,6),(69127,0,69624,0,7),(43652,2,312,65,6),(48224,1,396,18,6),(69203,0,69548,0,7),(44868,0,44731,0,7),(49412,0,49403,0,8),(160,256,23,72,6),(0,8,227,276,8),(1,32,94,384,7),(4,8,227,272,7),(43264,64,43197,2,9),(43048,0,43479,0,8),(44700,0,44899,0,7),(43538,4,353,136,6),(26,0,485,0,7),(48160,128,48475,4,9),(50760,4,305,130,6),(50784,1,396,18,6),(47641,0,48102,0,8),(69252,0,69499,0,11),(60036,0,60283,0,11),(59905,0,60398,0,11),(69253,0,69498,0,7),(58373,0,58874,0,8),(34,0,477,0,8),(16,256,135,104,7),(59970,4,305,136,6),(58434,4,305,136,6),(53777,2,424,68,6),(55425,2,312,68,6),(42912,0,42591,0,8),(9,0,486,0,8),(42820,0,42683,0,7),(46084,128,46427,32,9),(53826,1,396,48,6),(257,0,254,0,8),(58498,1,332,48,6),(52771,0,53212,0,7),(53024,0,52959,0,9),(256,32,94,129,7),(47712,1,396,18,6),(48292,0,48475,0,8),(49224,4,305,130,6),(44548,0,45051,0,12),(48385,0,48382,0,8),(46090,0,46581,0,8),(48132,0,48507,0,11),(2306,0,2237,0,8),(13825,0,14318,0,11),(43568,256,135,72,6),(69121,16,69606,8,9),(129,0,382,0,9),(60034,0,60285,0,9),(18561,0,18814,0,9),(44544,64,44733,258,10),(52736,64,52925,258,10),(2084,128,2395,0,8),(12546,0,12477,0,8),(26,4,353,128,5),(168,256,23,64,5),(1,16,486,8,9),(273,32,78,128,5),(296,16,198,1,5),(268,128,83,32,5),(292,128,91,0,5),(98,1,396,16,5),(21,2,424,64,5),(36,0,347,0,8),(273,0,238,0,7),(1864,0,1719,0,8),(388,0,123,0,7),(0,16,486,9,10),(0,64,189,258,10),(133,0,378,0,7),(74,4,305,128,5),(74,0,437,0,7),(152,0,359,0,8),(136,0,359,0,8),(266,64,181,0,5),(69194,0,69557,0,7),(44618,0,44981,0,7),(2,64,189,256,9),(321,32,30,128,5),(328,0,167,0,7),(256,64,189,2,9),(281,0,230,0,5),(58370,64,58557,256,9),(385,32,94,0,5),(32,128,347,4,9),(194,4,305,8,5),(260,128,91,32,6),(56,128,323,4,5),(58626,64,58557,0,8),(0,32,94,385,8),(49160,16,49638,1,9),(47968,0,47647,0,7),(42496,128,42843,36,10),(42528,128,42843,4,9),(43074,0,43453,0,11),(133,2,312,64,5),(200,4,305,2,5),(47944,0,47799,0,8),(4,128,347,32,9),(43008,64,43197,258,10),(59936,0,60383,0,12),(47776,0,47967,0,11),(67,0,428,0,7),(162,1,332,16,5),(388,64,57,2,5),(52896,0,53087,0,11),(297,16,198,0,4),(1164,0,1395,0,8),(185,0,326,0,4),(289,16,198,8,5),(154,4,353,0,4),(49,128,330,4,5),(334,0,177,0,4),(3,128,344,36,6),(324,8,163,16,5),(19,64,172,256,5),(70,128,281,32,5),(17,32,78,384,6),(321,0,190,0,7),(129,32,94,256,6),(18577,0,18798,0,8),(428,0,83,0,4),(15,16,480,0,4),(167,0,344,0,4),(59908,0,60283,0,11),(291,64,156,0,4),(56,256,135,64,5),(7,16,480,8,5),(275,64,172,0,4),(21,128,330,32,5),(112,1,396,2,5),(48,0,462,0,8),(456,0,55,0,5),(160,64,29,258,6),(288,128,91,4,6),(85,2,424,0,4),(178,1,332,0,4),(55297,16,55782,8,9),(416,64,29,2,5),(120,256,135,0,4),(72,4,305,130,6),(7,128,344,32,5),(43010,64,43197,256,9),(39,128,344,0,4),(98,128,281,4,5),(157,0,354,0,4),(162,64,29,256,5)]
def xmautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xmlevels : Nat → Packing
  | 15 => j170
  | 14 => j171
  | 13 => j172
  | 12 => j173
  | 11 => j174
  | 10 => j175
  | 9 => j254
  | 8 => j255
  | 7 => j256
  | _ => z38
def xmindex : Nat → Nat → Option (Nat × Nat)
  | 15 => z15 11 85 7 11 3 4 j176
  | 14 => z15 39 677 10 14 6 4 j177
  | 13 => z15 242 1097 11 17 9 4 j178
  | 12 => z15 715 2685 12 19 11 4 j179
  | 11 => z15 273 1027 11 18 10 4 j180
  | 10 => z15 24 113 7 14 6 4 j181
  | 9 => z15 3 19 5 11 3 4 j257
  | 8 => z15 1 7 3 9 1 4 j258
  | _ => fun _ => none
def xm15 : Forest := ⟨1535,15,fun j => xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem j223 : z84 xm15 (z8 z248) = true := by
  simp only [z84,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,z14 (d:=5) ?_⟩,z14 (d:=2) ?_⟩
  all_goals simp only [z40]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j36 : z13 xm15 15 0 1=true := by refine (z4 (ar:=9) (rows:=1) (d:=0) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j37 : z13 xm15 14 0 6=true := by refine (z4 (ar:=10) (rows:=1) (d:=1) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j38 : z13 xm15 13 0 46=true := by refine (@z7 xm15 13 0 16 30 (@z7 xm15 13 0 5 11 (z4 (ar:=9) (rows:=1) (d:=1) ?_) (z4 (ar:=10) (rows:=1) (d:=2) ?_)) (z4 (ar:=11) (rows:=1) (d:=3) ?_)); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q285 : z13 xm15 12 0 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q183 : z13 xm15 12 64 7=true := by refine (z4 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q182 : z13 xm15 12 71 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q94 : z13 xm15 12 135 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q93 : z13 xm15 12 199 29=true := by refine (z4 (ar:=11) (rows:=0) (d:=3) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q92 : z13 xm15 12 228 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q91 : z13 xm15 12 292 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q90 : z13 xm15 12 356 22=true := by refine (z4 (ar:=12) (rows:=0) (d:=3) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j39 : z13 xm15 12 0 378=true := (@z7 xm15 12 0 356 22 (@z7 xm15 12 0 292 64 (@z7 xm15 12 0 228 64 (@z7 xm15 12 0 199 29 (@z7 xm15 12 0 135 64 (@z7 xm15 12 0 71 64 (@z7 xm15 12 0 64 7 q285 q183) q182) q94) q93) q92) q91) q90)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q286 : z13 xm15 11 0 37=true := by refine (z4 (ar:=9) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q184 : z13 xm15 11 37 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q110 : z13 xm15 11 101 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q109 : z13 xm15 11 165 3=true := by refine (z4 (ar:=10) (rows:=0) (d:=0) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q108 : z13 xm15 11 168 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q107 : z13 xm15 11 232 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q106 : z13 xm15 11 296 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q105 : z13 xm15 11 360 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q104 : z13 xm15 11 424 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q103 : z13 xm15 11 488 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q102 : z13 xm15 11 552 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q101 : z13 xm15 11 616 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q100 : z13 xm15 11 680 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q99 : z13 xm15 11 744 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q98 : z13 xm15 11 808 1=true := by refine (z4 (ar:=11) (rows:=0) (d:=0) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q97 : z13 xm15 11 809 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q96 : z13 xm15 11 873 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q95 : z13 xm15 11 937 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q50 : z13 xm15 11 1001 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q49 : z13 xm15 11 1065 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q48 : z13 xm15 11 1129 64=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q47 : z13 xm15 11 1193 46=true := by refine (z4 (ar:=12) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j40 : z13 xm15 11 0 1239=true := (@z7 xm15 11 0 1193 46 (@z7 xm15 11 0 1129 64 (@z7 xm15 11 0 1065 64 (@z7 xm15 11 0 1001 64 (@z7 xm15 11 0 937 64 (@z7 xm15 11 0 873 64 (@z7 xm15 11 0 809 64 (@z7 xm15 11 0 808 1 (@z7 xm15 11 0 744 64 (@z7 xm15 11 0 680 64 (@z7 xm15 11 0 616 64 (@z7 xm15 11 0 552 64 (@z7 xm15 11 0 488 64 (@z7 xm15 11 0 424 64 (@z7 xm15 11 0 360 64 (@z7 xm15 11 0 296 64 (@z7 xm15 11 0 232 64 (@z7 xm15 11 0 168 64 (@z7 xm15 11 0 165 3 (@z7 xm15 11 0 101 64 (@z7 xm15 11 0 37 64 q286 q184) q110) q109) q108) q107) q106) q105) q104) q103) q102) q101) q100) q99) q98) q97) q96) q95) q50) q49) q48) q47)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q288 : z13 xm15 10 0 6=true := by refine (z4 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q287 : z13 xm15 10 6 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q185 : z13 xm15 10 70 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q118 : z13 xm15 10 134 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q117 : z13 xm15 10 198 64=true := by refine (z4 (ar:=10) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q116 : z13 xm15 10 262 21=true := by refine (z4 (ar:=10) (rows:=0) (d:=3) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q115 : z13 xm15 10 283 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q114 : z13 xm15 10 347 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q113 : z13 xm15 10 411 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q112 : z13 xm15 10 475 64=true := by refine (z4 (ar:=11) (rows:=0) (d:=4) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q111 : z13 xm15 10 539 5=true := by refine (z4 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem j41 : z13 xm15 10 0 544=true := (@z7 xm15 10 0 539 5 (@z7 xm15 10 0 475 64 (@z7 xm15 10 0 411 64 (@z7 xm15 10 0 347 64 (@z7 xm15 10 0 283 64 (@z7 xm15 10 0 262 21 (@z7 xm15 10 0 198 64 (@z7 xm15 10 0 134 64 (@z7 xm15 10 0 70 64 (@z7 xm15 10 0 6 64 q288 q287) q185) q118) q117) q116) q115) q114) q113) q112) q111)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j128 : z13 xm15 9 0 38=true := by refine (@z7 xm15 9 0 15 23 (z4 (ar:=9) (rows:=0) (d:=2) ?_) (z4 (ar:=10) (rows:=0) (d:=3) ?_)); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j129 : z13 xm15 8 0 5=true := by refine (@z7 xm15 8 0 2 3 (z4 (ar:=8) (rows:=0) (d:=0) ?_) (z4 (ar:=9) (rows:=0) (d:=0) ?_)); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem j130 : z13 xm15 7 0 1=true := by refine (z4 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [z20,z19,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q275 : z91 xm15 15 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact j130
  · exact j129
  · exact j128
  · exact j41
  · exact j40
  · exact j39
  · exact j38
  · exact j37
  · exact j36
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseM15 : z23 (z2 511) 15 (vars 1535).toFinset := by
  have h := q68 (g:=xm15) (i:=0) (ws:=vars 1535) rfl rfl (z6 z248 q268) j223 q275 (by decide +kernel)
  have hm : xm15.mask = 1535 := rfl
  have eg : z2 1535 = z2 511 := by decide +kernel
  simpa only [hm, eg] using h

end PEqualNP.Outside.L_meta_2116

theorem PEqualNP.Outside.L_meta_2116 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C hP hS
  exact PEqualNP.Outside.L_meta_2116.bound_2116 PEqualNP.Outside.L_meta_2116.caseU14 PEqualNP.Outside.L_meta_2116.caseM15 C hP.1 hP.2.1 (hP.2.2.1.trans rfl) hP.2.2.2.1 hS
