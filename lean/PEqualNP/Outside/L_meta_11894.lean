import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_11894.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

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

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

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

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
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
    · have hp := live_proper h z hm
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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
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

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
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
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

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

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
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

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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


end PEqualNP.Outside.L_meta_11894.Model

namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SB : Nat := 4

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_11894

namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def s0K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (5+((h/1+packedAt s0K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcf9ff8fc3ff39f
  | 2 => 0xffffffffffffffffffffffdff3fcff1ff87cf3
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff40602810250a4185
  | 2 => 0x2089010908912432
  | 3 => 0x150b506a42a52e18
  | 4 => 0xe221ab493064bc0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 30 s0Pos s0Neg, 0xfcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff0ff83ffff83e0fffffc1fc1fff93f27f
  | 2 => 0xf0783ff0ffc3c1ffc7f0e0f0fe1fe3c3ed4d93
  | 3 => 0xff803fff0003fe1ff800ff00ffe003fc718e1c
  | 4 => 0x3ffffffc001fffff0000fffffc007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10000100004000000001011000240040001025
  | 2 => 0x2512522252051309429068a25209428b254492
  | 3 => 0x4336b44636aab13ad988ba84f540cb39718e18
  | 4 => 0xa452888a420a454ad2a1008a99298105a0b40
  | 5 => 0x8c6630ecc733399f37ccdcce310312227fe000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 1 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 3 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 1 => 0x1212522244a90309434290a252144943294512
  | 3 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc7fff8787ff0ff0c3fe1ffe1c3ff0f8cf1cf
  | 1 => 0x87f8f0ff8070ff1ff0387e3c3e03c7f3cb4933
  | 2 => 0x7ff00ffff80ffe1ffc07fc03ffc07fc738e3c
  | 4 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80400008008001000000804400404100001045
  | 1 => 0x3492299115296831321c3228b20a9263494912
  | 2 => 0x41004222200280024440448104900488128228
  | 4 => 0x1434acc454482a559aad1022392b30216c0d80
  | 5 => 0x6626c887666ccc99ef367933903220ca7fe000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xfafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 2 => 0x22024888090049200948012202902514208c28
  | 3 => 0x441241aa5225402495d4900a1324ac14740e80
  | 4 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xfefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x860000001200008406883e00105a000e74780076624434601a520a244a2a92904e386c6a427e823c184836284c2c6e2e04728e540200308c5e40321c7c808a000022267a503a58561e00000c640800664670140016685c002000080220a00000001c025080008000303951854a84007fd50017f54007f95001fd54005f55001fc54007fd4c017f53007f94c01fd53005f54c01fc53007fd0c01fe43007f50c01fc43007fd48017f52007f94801fd52005f54801fc52007fd0801fe42007f50801fc42007fcc801df32007f8c801fd3200774c801fc32007fd44017f51007f94401fd51005f54401fc51007fd0401bf41007f90401fd41006f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd4001fe50005f94001fd50007f140017c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x184000bf18c20006fea6100037d53080017f3104000dfd4820006faa410003df3208001ee9904000bf98420007ecc210002f661080017eb084000fd58420005eac2100037f5108001bea884000efd04200077a8210002fe6008003bf2804001df14020007de4010003fa2008001f69004000fe48020005fecb88002fe65c4001bf32e20009f99710005facb880037d65c40013eb2e2000bf19710005fec988002fe64c4001df3262000af99310005fac988003bd64c40015eb262000bf19310006fea9880037d54c40017fb1e2000bf98f10005fac788002fc63c4001bfa9e2000df54f10005fec588002fe62c40017eb162000bf18b10006fea5880037d52c4001ef9962000f74cb10006fea388003f651c4001bea8e2000fd54710006eaa388003bf41c4001fb20e2000ef50710007ea8388003b541c4001fb18e2000fd4c710007ec4388003f521c4001bf2862000df14310005fecb080077f65840013fb2c2000bf99610005facb08002fc6584003be32c20009f19610005fec908002fe64840017eb242000bf19210006fea9080037d54840017fb1c2000bf98e10005fac708002fc6384001bfa9c2000df54e10005fec508002fe62840017eb142000bf18a10006fea5080037d5284001ef9942000f74ca10005fac3080037f5184001bea8c2000efd06100077a8308002fe6084003bf2842001df14210007f46108003f93084001fd1042000fe48210007ee2108003fb10840017fb2a2000dfd9510004feca88002fe65440017eb2a2000bf19510006f8ca880027c65440017fb222000bf99110005fac888002fc6444001bfaa22000df55110005fec688003df63440016fb1a2000bf98d10005fac688002fc6344001ee31a2000b718d10006fea6880037d53440017fb122000bf98910005fac488002fc6244001bfa922000df54910007be6488003dd3244001bfa8a2000fd94510006faa288003f55144001baa8a2000efd0510007ec8288003bd4144001faa0a2000ed50510007ec6288003f53144001fb10a2000fd48510006fca0880037c5044001fd1822000fe4c110007f44088003f92044001fd8822000fd84110005feca08002fe6504001bf32820009f99410005faca080037d65040013eb282000bf19410005fec808002fe6404001df3202000af99010005fac808003bd64040015eb202000bf19010006fea8080037d54040017fb182000bf98c10007bcc608002de63040017eb182000f758c10005bac608002fc6304001bfa982000df54c10005fec408002fe6204001f73102000bb98810005fac408003ed620400176b102000bf18810006fea4080037d5204001ef9902000f74c810005fcc2080037f5104001bea882000efd04100077a8208002fe6004003bf2802001df14010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3dd324c0017fb0a6000bf18530006fea2980037d514c001dfa0a6000ef50530007be6298003dd314c001bf2826000df14130007f66098003de304c0017fb286000bf99430006fcca180027e650c0017eb286000df59430004faca18002fc650c0017fb206000bf990300077cc818002be640c0017eb206000ef590300057ac818002fc640c001bfaa06000df55030005fcc6180037f530c001bea986000bf98830007dcc418002ee620c0017eb106000fb58830005dac4180037f520c001bea906000f7cc830007ba6418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000dfd4430006faa218003bf410c001dea086000f78c430007b86218002fe600c003bf2806001df14030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c8001bf32e40009f99720005facb900037d65c80013eb2e4000bf19720005fec990002fe64c80017eb264000bf19320006fea9900037d54c80017fb1e4000bf98f20007bcc790002de63c80017eb1e4000f758f20005bac790002fc63c8001bfa9e4000df54f20006fea590003ee52c8001bea964000fb54b20006daa590003ee42c8001f6a164000f7ccb20007dc6590003dd32c8001f69964000f34cb20005fcc390002fd61c8001bfa8e4000df547200077e8390003bd41c8001f790e4000fb48720006fca1900037c50c80017fb2c4001dfd9620004fecb10002fe65880017eb2c4000bf1962000ef8cb100027c65880017fb244000bf99220005fac910002fc6488001bfaa44000df55220005fec710002fe63880017eb1c4000bf18e20006fea7100037d53880017eb144000dfd4a20006faa510003df3288001ee9944000bf98620005fac3100037f5188001bea8c4000efd06200077a8310002fe6088003bf2844001df14220007f48110003f94088001f79044000fec8220005feca900037f65480013fb2a4000bf99520005faca90002fc6548001be32a40009f19520005fec890003bf64480015fb224000bf99120005fac890002fc6448001de3224000af19120006fea8900037d54480017fb1a4000bf98d20005fac690002fc6348001bfa9a4000df54d20006fea490003ee5248001bea924000fb54920006daa490003ee4248001f6a124000f7cc920007dc6490003dd3248001f69924000f34c920005fec290002fc6148001bfa8a4000df545200077e8290003bd4148001f790a4000fb48520006fca0900037c5048001fd2024000fe50120007f64090003ee20480017fb284000bf99420006fcca100027e65080017eb284000df59420004faca10002fc65080017fb204000bf990200077cc810002be64080017eb204000ef590200057ac810002fc6408001bfaa04000df55020005fec610002fe6308001ef3184000b798c20005fac610003dd63080016eb
  | 2 => 0x400077a83a00037e50d0001be2868000bfd964000efecb200027f65900017f32c8000bf59640005f8cb200077c65900013e32c8000bf59240006fea9200037d54900017f31c8000bf58e40006fea7200037d53900017f3148000bf58a40006fea5200037d5290001df2148000ef10a40007be6520003dd32900017f30c8000bf58640006fea3200037d5190001dfa0c8000ef50640005fcc1200077e5090003be2848000efd0240007f68120002ff6550001bfb2a80009fd9540005fccaa0002fd65500017e32a8000df19540004f8caa00037f5450001df2a28000df551400077aa8a00033d54500017fb1a8000bf18d40006fea6a00037d5350001dfa1a8000ef50d40005fec4a0002fc6250001bfa928000df549400077e84a0003bd4250001ef9928000f74c940005fec2a0002fc6150001bfa8a8000df545400077e82a0003bd4150001bf2828000df14140007f680a0003be40500017fb288000bf99440006fcca200027e65100017eb288000df59440004faca20002fc65100017f3208000dfd5040006faa820002fe6310001ef3188000b798c40005fac620003dd63100016eb188000dfd4c40006faa620002fe6210001f73108000bb98840005fac420003ed621000176b108000dfd4840006faa420003be4210001de2108000f7cc840007ba6420002fe6110001fb3088000bd98440005fac220003f561100017ab088000dfd4440006faa220003bf4110001dea088000bf9804000efca0200077c5010001dfa008000fe900400077a8020003f940100017fb2e6000bf99730006fccb980027e65cc0017eb2e6000df59730004facb98002fc65cc0017fb266000bf99330005fac998002fc64cc001bfaa66000df55330006fea798003de53cc001bea9e6000f754f30006baa798003de43cc001eea1e6000bf98b30005fac5980037f52cc001bea966000f7ccb30007ba6598002fe61cc0017eb0e6000dfd4730006faa398003bf41cc001dea0e6000f7cc730007ba63980037e50cc001be2866000bfd963000efecb180027f658c0017f32c6000bf59630005f8cb180077c658c0013e32c6000bfd9230005fcc918002fd648c0017e3246000dfd5230006faa918002fd638c001bfa9c6000df54e30005fcc518002fd628c001bfa946000df54a30007be6518003dd328c0017f30c6000bf58630006fea3180037d518c001dfa0c6000ef50630007bc6318003dc318c0017f3046001df9423000ef8a118003df308c001fd9846000bfd9530006feca980027f654c0017f32a6000bf59530005f8ca980037c654c0013e32a6000bfd9130005fcc898002fd644c0017e3226000dfd5130006faa8980037f534c001ef29a6000df54d30007baa6980035d534c001ef21a6000f750d30005fec498002fc624c001bfa926000df54930007be649800
  | 3 => 0xe28ca000efd06500077a8328002fe6094001bfa84a000fed425000efec9280037e6494001beb24a0009f5925000ef8c9280077f6394001bf31ca000df58e50004fac7280077c6394001bfa1ca000df90e50006fa87280037c4394003bfb14a000df98a50006fac5280027d6294003be314a000dfd0a50006fc85280037d4294001be214a000dfcca50006be65280037e3294001be994a000d74ca50006f865280077f6194001bf30ca000df58650004fac3280077c6194001bfa0ca000cfd0650006fc83280037d41940019ea0ca000df10650006fe63280037e3194001be98ca000df0c650006fe43280037e2194001be90ca000df08650004fcc128002ff64540017e322a000dfd5150006faa8a8002ff63540017e31aa000dfd4d50006faa6a8002ff62540017e312a000dfd4950006faa4a8003df3254001ee992a000bfd8550005f8c2a80037f5154001bea8aa000efd05500077a82a8003fb5054001bf282a000bf99450005fcc828003be64140015f320a000bf590500077ac828002bd6414001bfaa0a000df95050006faa8280037c54140017f318a000f798c50005bcc628002fd6314001eeb18a000b758c50006fea6280037e5314001bea98a000df14c50005fcc428003ee621400177310a000bf58850007dac428002ed6214001bfa90a000df94850006faa4280037c5214001ef990a000f74c850005fcc228003f661140017b308a000bf58450007eac228002f56114001bfa88a000df94450006faa2280037c5114001dfa08a000ef50450005fcc0280037f5014001fd280a000df54050007f2a0280077f6414001bf320a000cf99050006fac8280027d64140019eb20a0008f5905000ef8c8280077f6314001bf318a000d798c50006fac6280027d6314001aeb18a0009758c5000ef8c6280037f4314001bf218a000df50c50006f886280077f6214001bf310a000db98850006fac4280027d6214001b6b10a0009b5885000ef8c4280037f4214001bf210a000df50850006f884280037f3214001af990a000df8c850006fa64280035d3214001be190a001dfd8450006fcc228003766114001beb08a0009f58450006eac228002756114003be308a000dfd04500067e82280037e4114001bea08a000cf50450006f882280037f3114001bf188a000df4c450006f862280037f2114001bf108a000df48450006f842280077e60140013f300a000de98050005fecba0002fe65d0001bf32e80009f99740005facba00037d65d00013eb2e8000bf19740006fea9a0003be54d0001beaa68000ef553400067aa9a0002fe63d00017eb1e8000dfd4f40006faa7a0003bf43d0001dea1e8000bf98b40005fac5a00037f52d0001bea968000efd0b400077a85a0003df32d0001ee9968000bf98740005fac3a00037f51d0001bea8e8000efd07
  | 4 => 0x803b5410c401ef9886200fd8c431007ba6218803f5310c4017f3006200fe98031005f4c018802fd600c401fcb006200be58031005fecb90802fe65c8401bf32e42009f99721005facb908037d65c84013eb2e4200bf19721005fec990802fe64c84017eb264200bf19321006fea9908037d54c84017fb1e4200bf98f21007bcc790802de63c84017eb1e4200f758f21005bac790802fc63c8401bfa9e4200df54f21006fea5908037d52c8401ef9964200fb8cb21007ba6590803ed32c8401e69964200dfd4721006faa390803bf41c8401dea0e4200bf98321005fac190802ff65884017f32c4200df99621004fccb10802fd6588401beb2c42009f59621005f8cb10802ff64884017f3244200ef992210057cc910802fd6488401deb244200af59221005f8c9108037f5488401beaa44200bfd8e21005fcc710802fd63884017e31c4200dfd4e21006faa710802fd6288401bfa944200df54a21007be6510803dd32884017f30c4200dfd4621006faa310803bf4188401fb20c4200ef50621007ea8310803b54188401f790c4200fdc8621005fcc110802fd60884017fb2a4200bf99521006fcca908027e65484017eb2a4200df59521004faca90802fc65484017fb224200bf99121005fac890802fc6448401bfaa24200df55121005fec690802fe63484017eb1a4200bf18d21006fea6908037d5348401bfa924200df54921007be6490803ee3248401ee9924200fb4c9210079a64908037f5148401bea8a4200efd0521007ec8290803bd4148401faa0a4200ed50521007ee4290803ee21484017fb024200bf18121005feca10802fe6508401bf32842009f99421005faca108037d65084013eb284200bf19421005fec810802fe6408401df3204200af99021005fac810803bd64084015eb204200bf19021006fea8108037d54084017fb184200bf98c21007bcc610802de63084017eb184200f758c21005bac610802fc6308401bfa984200df54c21005fcc4108037f5208401bea904200f7cc821007ba6410802fe6108401bfa884200df544210077e8210803bd4108401f79084200fd88421007da4210803f521084017f3004200fe98021005f4c010802fd6008401fcb004200be58021005fcc9a8002fd64d4001bfaa6a000df55350005fcc7a8002fd63d4001bfa9ea000df54f50005fcc5a8002fd62d4001bfa96a000df54b50007be65a8003dd32d40017f30ea000bf58750006fea3a80037d51d4001dfa0ea000ef50750005facb28002fe64940017eb24a000dfd5250006fca9280037d5494001be2a4a000bf98e50005fac7280037f5394001bf29ca000df54e50006f8a728002fe62940017eb14a000dfd4a50006fca5280037d5294001be294a000f7cca50007ba6528002fe61940017eb0ca000dfd4650006fca3280037d5194001b
  | 5 => 0x8141005f8c0a0803bf6550401df32a8200cf995410077acaa08033d6550401de32a8200efd8d410077cc6a0803bd6350401de31a8200efd4d410067ea6a0803be5350401dea9a8200cf54d4100778a6a0803bf6250401df3128200ef5894100778c4a0803bf52504019fa928200ef949410077aa4a08033d5250401de2928200efcc9410073e64a0803be3250401de9928200e74c9410077864a0803bf6150401dbb0a8200efd45410067ea2a0803be5150401dea8a8200cf5454100778a2a0803bf6050401df3028200ef5814100778c0a0802ff65104017f3288200df99441004fcca20802fd6510401beb2882009f59441005f8ca20802fe64104015f3208200dfd5041006faa820802fe63104017eb188200dfd4c41006faa620802fe62104017eb108200dfd4841006faa420803df3210401ee9908200bf98441006fea2208037d5110401dfa088200fd904410077a8220803f541104017f3008200bf58041005fecb98802fe65cc401bf32e62009f99731005facb988037d65cc4013eb2e6200bf19731005fec998802fe64cc4017eb266200bf19331006fea9988037d54cc401bfa9e6200df54f31005fcc598802fd62cc401bfa966200df54b31007be6598803dd32cc401bfa8e6200df547310077e8398803f641cc401dea0e6200fd507310076a8398802fe60cc4017eb066200bfd9631005fccb188037e658c4013f32c6200bf59631006facb188027d658c4017e32c6200bfd9231005fcc918803be648c4015f3246200bf592310077ac918802bd648c4017e3246200dfd5231006faa918802fd638c401bfa9c6200f794e31006faa718803dd538c401aea9c6200f790e31007ba8718802fe628c4017eb146200dfd4a31006faa518803df328c401ee9946200bf98631006fea3188037d518c401dfa0c6200ef50631007be6318803f7318c4017f3046200bf58231005feca98802fe654c401bf32a62009f99531005faca988037d654c4013eb2a6200bf19531005fec898802fe644c4017eb226200bf19131006fea8988037d544c401bfa9a6200df54d31005fec498802fc624c401bfa926200df54931007be6498803dd324c401bfa8a6200df545310077e8298803bd414c401fb98a6200f78c531005fec098802fc604c4017fb286200bf99431006fcca188027e650c4017eb286200df59431004faca18802fc650c4017fb206200bf990310077cc818802be640c4017eb206200ef590310057ac818802fc640c401bfaa06200df55031005fcc6188037f530c401ef2986200df54c31007baa6188035d530c401ef2186200f750c31005fcc418803ee620c401773106200bf58831007dac418802ed620c401bfa906200df54831007be6418803dd320c4017f3086200dfd4431006faa218803bf410c401fb2086200ef50431007ea8218
  | 6 => 0x1ee992a200fdd4551006fca2a8802ff60544017e302a200dfd9151004fec8a88037e6454401beb22a200df19151006fec6a88027f6354401bf31aa200df58d51006f8c6a88037f4354401bf21aa200df50d51006f886a88037f62544013fb12a200df98951006fac4a88037c6254401bfa12a200df90951006fa84a88037c4254401bf992a200d7cc951006fc64a88037d3254401ae992a200df0c951006fec2a8803776154401bfb02a200df98151006fac0a88037c60544013e302a200bf99451004fcca28802fe6414401df320a200af99051005fac828803bd64144015eb20a200dfd5051006faa828802fe63144017eb18a200dfd4c51006faa628802fe62144017eb10a200dfd4851006faa428803df3214401ee990a200bf98451006fea228803f65114401bea88a200fd54451005fcc028802fd60144017fb2e8200bf99741006fccba08027e65d04017eb2e8200df59741004facba0802fc65d0401bfaa68200efd53410067ea9a0803be54d0401beaa68200ef553410067aa9a0803bc54d04017f31e8200f798f41005bcc7a0802fd63d0401eeb1e8200b758f41006fea7a08037d53d0401dfa1e8200ef90f410077a87a0803bc43d04017f3168200bf58b41006fea5a08037d52d0401dfa168200ef90b410077a85a0803bc42d0401ef9968200f74cb41006fea3a08037d51d04017f3068200bf583410077ecba0803be65d04019f32e8200ef597410067acba0803bc65d0401dfb1e8200ef98f410073cc7a0803bd63d0401ceb1e8200ef18f410077ea7a08033f53d0401df29e8200ef54f410067aa7a0803bc53d0401dfb168200ef98b410077ac5a0803bc62d0401dfa968200cfd4b410077ca5a0803bd52d04019ea968200ef14b410077e65a08039f32d0401df1968200ef4cb410073a65a0803bc32d0401dfa8e8200cfd47410077ca3a0803bd51d04019ea8e8200ef147410077ec1a0803be60d0401deb068200ef18341005fecb20802fe6590401bf32c82009f99641005facb208037d65904013eb2c8200bf19641005fac920802bd6490401bfaa48200df55241005fcc720802fd6390401bfa9c8200df54e41005fcc520802fd6290401bfa948200df54a41007be6520803dd32904017f30c8200dfd4641006faa320803bf4190401fba0c8200bf98241005fac120802ff65504017f32a8200df99541004fccaa0802fd6550401beb2a82009f59541005f8caa08037f5450401dfaa28200cfd51410077ca8a08037d5450401deaa28200cf5514100778a8a0802ff63504017e31a8200dfd4d41006faa6a0803bf4350401df21a8200ef50d410077886a0802ff62504017e3128200dfd4941006faa4a0803bf4250401df2128200ef509410077884a0803df3250401ee9928200dfd4541006faa2a0803f74150401df20a8200bfd
  | 7 => 0x19002fe628c801bfa946400df54a32007de8519003ec428c801ef9946400fbcca32005fcc319002fd618c8017f3046400bf58232005feca99002fe654c801bf32a64009f99532005faca990037d654c8013eb2a6400bf19532005fec899002fe644c8017eb226400bf19132006fea8990037d544c801bfa9a6400f7d4d32006bea699003de534c801bea9a6400f754d32006baa699003dc534c801efa1a6400f790d32007ba8699003dc434c801bfa926400df54932007de8499003ec424c801f79926400f78c932005fec299002fc614c8017fb026400bf18132007beca99003de654c801af32a6400f759532006baca99003dc654c801efb226400f799132007bac899003dc644c801efaa26400d7d5132007bca899003dd544c801aeaa26400f715132007bec499003cf624c801efa926400d7d4932007bca499003dd524c801aea926400f714932007be8499003cf424c801ef2126400f750932007b88499003cc424c801efb0a6400f798532007bac299003dc614c801efb026400f798132007bac099003dc604c8017fb286400bf99432006fcca190027e650c8017eb286400df59432004faca19002fc650c8017fb206400bf99032005fac819002fc640c801bfaa06400df55032005fcc619002de630c801bfa986400df54c32005fcc4190037f520c801bea906400f7cc832007dc6419003dd320c801f69906400bf98432005fac219002fe600c8017eb006400bf99351005fac9a88037f54d4401bf2a6a200df55351006f8a9a8802fe63d4401ef31ea200b798f51005fac7a8803dd63d44016eb1ea200dfd4f51006fca7a88037d53d4401be29ea200bf98b51005fac5a88037f52d4401bf296a200df54b51006f8a5a8803df32d4401ee996a200bf98351005fac1a88037f64d4401bf326a200df59351004fac9a88037c64d4401bfb1ea200df98f51006bcc7a88037d63d44013eb1ea200d758f51004bac7a88037c63d4401bfa1ea200df90f51006fa87a88037c43d4401bfb16a200df98b51006fac5a88027d62d4401be316a200dfd0b51006fc85a88037d42d4401be216a200dfccb51006be65a88037e32d4401be996a200d74cb51006f865a88037f60d4401bf306a2009f98351006fac1a88037c60d44017eb2ca2009f59651005fcc928803be64944015f324a200bf592510077ac928802bd6494401bfaa4a200df55251005fcc728802fd6394401bfa9ca200df54e51005fcc528802fd6294401bfa94a200df54a51007be6528803dd32944017f30ca200dfd4651007eea328802fe60944017eb04a200bfd9151005f8c8a88037f5454401bf2a2a200df55151006f8a8a8802ff63544017e31aa200dfd4d51006fca6a88037d5354401be29aa200bfd8951005f8c4a88037f5254401bf292a200df54951006f8a4a8803df325440
  | 8 => 0xf58c52007bac629002dd6314801bfa98a400df54c52005fcc4290037f5214801f7290a400df54852007daa429002fe61148017eb08a400bf98052005fac029002ff65d08017f32e8400df99742004fccba1002fd65d0801beb2e84009f59742005f8cba10037f54d0801beaa68400bf98f42005fac7a10037f53d0801bea9e8400dfd4b42006faa5a1002fe61d08017eb0e8400bf98342005fac1a1002ff65908017f32c8400df99642004fccb21002fd6590801beb2c84009f59642005f8cb21002fd6490801bfaa48400ef95242006faa921003bd54908019eaa48400bf98e42007bcc721002de63908017eb1c8400f758e42005bac7210037f5390801bea9c8400efd0e420077a8721002fe6290801bfa948400df54a420077e8521003ef42908017f30c8400bf58642005fcc121002fd60908017fb2a8400bf99542006fccaa10027e65508017eb2a8400df59542004facaa1002fc6550801bfaa28400df55142005fec6a1002fc6350801bfa9a8400df54d42006fea4a10037d5250801f7a128400ef90942005fec2a1002fc61508017fb028400bf18142005feca21002fe6510801bf32884009f99442005faca210037d65108013eb288400bf19442005fcc8210037f5410801df2a08400df550420077aa8210033d54108017f3188400f798c42005bcc621002fd6310801eeb188400b758c42006fea6210037d5310801dfa188400ef50c42005fcc4210037f5210801bea908400efd0842007dc8421003bd4210801f6a108400bf98442007ecc221002f661108017eb088400fd58442005eac221002fe6010801fd3008400be98042005fac021003f960108017cb008400bfd9732005fccb990037e65cc8013f32e6400bf59732006facb990027d65cc8017e32e6400bfd9332005fcc999003be64cc8015f3266400bf593320077ac999002bd64cc8017e3266400dfd5332006faa9990037f53cc801efa9e6400d7d4f32007bca7990037d53cc801eea9e6400d754f32007b8a799003df43cc801ef21e6400f750f32007b887990037f52cc801bea966400bf98732005fac399002fe60cc8017eb066400f7d9732007bccb990035e65cc801eeb2e6400d759732007b8cb99003df64cc801ef3266400e799332007bac9990039d64cc801ee3266400f7d5332006bea999003de54cc801eeaa66400d755332007b8a999003df52cc801afa966400f794b32007baa5990035d52cc801ee2966400f7d0b32007bc8599003dd42cc801ee2166400f7d8732007bcc399003dd61cc801ee30e6400f7d8332007bcc199003dd60cc801ee3066400bfd9632005fccb190037e658c8013f32c6400bf59632006facb190027d658c8017e32c6400bfd9232005fcc919002fd648c8017e3246400dfd5232006faa919002fd638c8016eb1c6400dfd4e32006faa7
  | 9 => 0xc01bea98a600f754c53005fcc429802fd6214c017f308a600bf58453005fcc029802fd6014c017fb2e8600bf99743006fccba18027e65d0c017eb2e8600df59743004facba1802fc65d0c01bfaa68600df55343006fea7a18037d53d0c017f3168600bf58b43005fcc3a1803f661d0c017b30e8600bf58743007eac3a1802f561d0c017f3068600bf58343005fecb21802fe6590c01bf32c86009f99643005facb218037d6590c013eb2c8600bf19643005fac9218037f5490c01beaa48600bf98e43006fea7218037d5390c01dfa1c8600f7d0e43005fcc521803ee6290c01773148600bf58a43007dac521802ed6290c017f30c8600bf58643005fcc121802fd6090c017fb2a8600bf99543006fccaa18027e6550c017eb2a8600df59543004facaa1802fc6550c01bfaa28600df55143006fea6a18037d5350c01efa1a8600ef90d43005fec4a1802fc6250c017fb0a8600bf18543005fec0a1802fc6050c017fb288600bf99443006fcca218027e6510c017eb288600df59443004faca21802fc6510c017f3208600dfd5043006faa821802fe6310c01bfa988600df54c430077e8621803de4310c01dea188600f750c43005fcc421802fd6210c017f3088600bf58443005fcc021802fd6010c017f326a400ef993520057cc9a9002fd64d4801deb26a400af59352006fea9a90037e54d4801beaa6a400df15352005fcc7a9002fd63d4801bfa9ea400df94f52006faa7a90037c53d48017f30ea400bf58752005fcc1a9002fd60d4801bfb26a400df993520067cc9a90037d64d48013eb26a400cf593520047ac9a90037c64d4801bfb1ea400df98f52006fac7a90027d63d4801be31ea400dfd0f52006fc87a90037d43d4801be21ea400dfd8752006fcc3a90037d61d48013eb0ea400df18752006fec1a90037e60d48013f306a400df58352006f8c1a9002fd65948013eb2ca400bf99252005fac9290037f5494801beaa4a400bf98e52007bcc729002de63948017eb1ca400f758e52005bac7290037f5394801bea9ca400bf98a52006fea529003ef52948017f30ca400bf58652005fcc129002fd60948017fb22a400bf19152006fea8a90037e5454801beaa2a400df15152005fec6a9002fc6354801bfa9aa400df94d52006faa6a90037c5354801f7a92a400df94952005fec2a9002fc61548017fb02a400bf18152006fec8a90027f6454801bf322a400df59152006f8c8a90037f63548013fb1aa400df98d52006fac6a90037c6354801bfa1aa400df90d52006fa86a90037c4354801bfb12a400dbd8952006fec2a90027f6154801bf30aa400df58552006f8c2a90037f6054801bf302a400df58152006f8c0a90027c60548017f328a4009f99452005fcc829002fd6414801bfaa0a400df55052005fcc629003de63148016f318a400b
  | 10 => 0x80000980300780200100000000100180680700200180000000800700000100000c00180000100080100080480280000000080580000400200080700900d02980700000780480700000100000180000000080080780000300280180080000100400600000001000680080000380000100380081000000000380000001980600080100000600780000180200000680000180000100080080180081400600200780000100c00380a809002800000001000805013000800001800801802fe63d50017eb1ea800bf98b54005fac5aa002fe61d50017eb0ea800bf98354005fac1aa0037f63d5001bf31ea800df58f54004fac7aa0037c63d5001bfb16a800df98b54006fac5aa0027d62d5001be316a800dfd8754006fcc3aa0037d61d50013eb0ea800df18754006fec1aa0037e60d50013f306a800df58354006f8c1aa002fd65950013eb2ca800bf99254006fea92a003bf54950019faa4a800bf98e54005fac72a002fe62950017eb14a800bf98654005fac32a002fe60950017eb04a800efd5154006fca8aa002ff63550017e31aa800bfd8954005f8c4aa002ff61550017e30aa800bfd8154005f8c0aa0037f64550019fb22a800dfd8d54004fec6aa0037e6355001beb1aa800df18d54006fec4aa0027f6255001bf312a800df58954006f8c4aa0037f61550013fb0aa800df98554006fac2aa0037c6155001bfb02a800df98154006fac0aa0037c60550013e302a800bf99454004fcca2a002fe6415001bfaa0a800ef95054006faa82a003bd54150017f318a800bf58c54005fcc42a002fd62150017f308a800bf58454005fcc02a002fd60150017f326a600bf59353006fea9a98037e54d4c01beaa6a600df15353005fcc5a9802fd62d4c017f30ea600bf58753005fcc1a9802fd60d4c01bfb26a600df99353006fac9a98027d64d4c01be326a600dfd8b53006fcc5a98037d62d4c013eb16a600df18b53006fec3a98037e61d4c01beb0ea6009f58753006f8c3a98037f60d4c01bf306a6009f98353006fac1a98037c60d4c017eb2ca6009f59653005fcc929802fd6494c01bfaa4a600df55253005fcc7298037f5394c01efa9ca600bf98a53005fac529802fe6194c017eb0ca600bf98253005fac129802ff6454c017e322a600dfd5153006fca8a98037d5454c01be2a2a600f7d4d53006fca6a9802ff6254c017e312a600bfd8553005f8c2a9802ff6054c017e302a600dfd9153004fec8a98037e6454c01beb22a600df19153006fec6a98035f6354c01bfb12a6009fd8953006fcc4a98037d6254c01be312a600dfd8553004fec2a98037e6154c01beb0aa600df18553006fec0a98037e6054c01beb02a600df18153004f8c0a9802fe6514c013f328a600bf99053005fac8298037f5414c01beaa0a600bf98c53006fea629803de5314
  | 11 => 0x1c4c0003ad34680001e82d300180400000080080000780080000080080000280300180000300900000000300000280400180080000000800080180300000000000400080380080000200080000180000380180000000100000200000280400080480181282300000280380100000a80000b80100300080000080c80500380100a00680100200000000580000500180100081300001e00000000000000200180200601c80000200a00f00280000000180100680100000100080180300080b80000280180700200080582f00000581600000380000000000600180000580a00400000000080080580100080380000080100d00200080200280300080301280280800100180200080600180700000080200000180000000000400180180200280000300100000700080080100800000800082900200480000200280400700200080080200000880000680000080000700000100100080000000000100080700080080000000100300000780200000900100280080280a80000600880380300300080800000180000100e80180000200100000200000980200600000100300000380b80000100380300000200400b80280f00080080100200000600300c80000080400000400180000000100000200380000180100081000000300000600280900300000100000000180500080100180480200680180700001280700000580500800500000280200000d80000100400400180200000080180000680080000000100400c80000200080d80000000180080000380580300100200000000680c00080c80180000200001280000700080000000000100080880080000180000000680180300200100201000200280000000000080080000080080780800080780000000180280100500000001080000080080000600000080000100001a80a80280300680000000000800100300380580180180800a80080a80080000680a80280080200100300380500100400180080000180080080180300080000100380580200382d00080180200000780300100100000000100080280180000200000400500180100000380780000000100e80080000280000000100000100200380500a80200080080080480080000980500000000080000780580000003000100a00080c80c80100000080080001280600101881880080280280c80100180080280800000000180000300180100380000000000000280400700800200480000380880200380180601600000100b80000080400600100380080300100200000100800000200d80580100100500101780000680480300780380080200100100400000080300000080080000000700400100000480100880100300380300200880280180080000681480280780000080000780000000080100800000080c0008000040038008
  | 12 => 0xf88aba0632d900004da04e38f0eecdc26651ac0a991244d40000fcc53090f1728b407c43c30001ecc7785810000000f4a0001379f700004fd11798a8c880000000f70a5a34807904ec4240000001b300000002ee233c8dc77144b17d859a49f28784710a000000001591923131ff105064a6fe00007983184eb00000007ae0001d39de087a1be0000ea053e46f0001af40001751080ab8000052288800000028a456024400033b000000000082a0001d780004640000000eb01a144788f014c56a4a10db09a63ae165941d28c07200000004fe44f37c0cc80008bf1022000d765570822530aa60000b98000f9884e0002398b9053f000230000001b00000006682181418c2c9a41d2047044c000000103000057e4af05517dce120000eb8d240fa6a30000c58d200000028c1111a8242858000230497401000007253208b01a915400a39e13200000002de8e040007c20002250eb44d61b20f485ce8d20000000f688093388000d347c808424c400000000018e8ca04cf2d2a51084053b1759a3cae400028d982026872a35702645544be03c2290f5e30242a8cb05dc8200879e30b5661e3d700506381221af8bcc0000da09e182c78e80f00009e49a277c14924bc2bc0d43eb010400092715487f800000000003810e005c0000000f0c51f000000102e1c20aa0000340712383000100a81236d80a494802d354850c9840000619bc43048a842196740960004a296103987d43970a70e1456f2e282041f88fd21188289b65d541d1ddd2825e82af0fc81a44031831a7899641f48ba50035404d28480004be1a63cf88f820e37e44c0518e6228e2ca92cc0003441c2881c1fe31a2ed0000cc81d8000116072c73e00d0040352794000077ccd65b10000e68000000279929906a0003099d903e64bd41617b09508580000c901040b30b8242000067c35e00001ee3f902a800000000000015952328f300011ec00089100021e0b5800043b8000f8e89a0001c140002580001dbd1445ee19a969c64224c21722e50e44ff3c296f90c01513fc0390b0a67b0f80e741a200041b1d585686380c781100003b0000000000082d3d0000060094b1400184cdc0000a20000d7e1d608e973441c0000a70000d546fa0001e000000e92c9835864c5204502390b2e3fd3a40ee81380182ac17ec98c59b1210000f4c80c131a03437854e3860000e7290100000000000cf35d03610f41931238b709c00ba2450af400019a39992850ba0000000dc12a400017e000000000000012609cc8033ce80012606c70000f3cbb291000023107ea0313732204e3e6cf04d1de8e6c44d2289d745928b5256169845400327b9a547b69203101d643c225621504dc0dc6f30000000b3e2d10948000000923000000000072600000011e04b9000000049a0002e813b82d20003f880009bc0
  | 13 => 0x1b60c847410000000ee6000000000000046247696400000000000000f587030fd800000026200000011d885a2a780011ae00000000000000000431860f7200037d98b800030a000066400086111e86b80001c507e834cee40001a712880000070001814e2204536a80000f20000a497c87aa0003d18000e421bf472800107c00000009ac000000000000107223a3a994b000010307d0f0430854100e01ecaea00016400000006cb35a939107a2e630f8290584000000000006c0003738000ad000038702b818200023a00011d605f303000000074923696a4c220000cd88e44487d842318c80000001c79fec0008750000c202fc55f3a523291163a049b0fb83d886246e90e40003200002320e7e8370a1214454a6282f8804cb8c0cd16c02c473271b37b158415a16130493640d280411580e8ce039747d88c4b7843f23c89d929204819483d83f44ab25d0054a2e6142338cb84f849013d8b046bc07404611ac624268100102029847029a995c93645437f82f862e5b424617891a805a09c96682e408a27d03411207fd0e78df492a19c1918b304b24b710da1a12388213508770a446631e8230cae00001e880b80000001148a9ccf45890001f3800057601584906ca1904129200a0025d01e8ac89d48534558648d3800012703ecd025270000310ab43e62d18d3434406535695105ae120080869413073a1a3a44459e126000194521c2ec3cf11487e200016523d4dd64cd36d00005b68b43620be40ee0c23c9056472a3910000000ea868e46fa358000551000000000039e1da8ded0226d939ba1910a85740001aa000000000002e400066100019181900dd000025871635a00022b8ada5b7420970ce5067516700000007de00013c81d803b468974c00000000009044c22532840000a5e0000002100092000436997c8b20093981a6c70c5303ff9548ec681e05f800103430c0fe0ba87be48e0c3000031400043999b4cfa1a733600000000000001f9c85676a1568bc8bfa1f13c20b58f1c0000cb8000f7a00044495150ac63b3189ab039c00018d921c68c0003c9972460e25a40a09a41dc01e00005bc0000002519224afe0000001e2000060014f0f645863ec000000000000000000004941ba2cc80006b277542b90908327fe411022c00085e000127404e00009704ccc8a0002308a8842a20d2189bbca9a3e32090a1866e00000016bd17a7f2117246c0008fc18299504e80000001c04f0e74f17085d85e87ee0001b9400000020f10d00003e544123a400050a3dc16487367c31d19f10aac2b720a8324e00000469854800094835c9ba51f400034483390848d825a8f4c79c1353a19a1c38c610000000046e3cd22b8b1066c5ad116000046c1de0c1985d1700041ea120d24a932369875408c79847c9000f4892d0880dfc78018e3039
  | 14 => 0x95dc5080000000cc0a9403f2f680011c40002b185a00000001010b180000000001f340008e72180000a6c194000188800069d0000f2800000026180000007240001e6cd7c8cd1e217040000f8106000000053c2271970bf800006b96506b800017d177cf500002c7827914c0c7282000127c240383992022e0004238cad2b40de00309e00005c240520401c481c00007f50300003dd1e5d12a1c426b9edc7104423eb9be50de78d0ab00000000000000e28d622fd2009c405020003f8147400025007305892b28c50000da400021928a8c40fa217400020a4ce848443b01c43000001ca000043a7252d09b0885200003b227cefa8f42cb23549d80660ad20a04b693b02f24585326261be000056a90037e0000cb400007f04e80ba85c386867ccc4000000059c7004ef287000000066800009cc73e0003821508000000264800000000016900007ba32800000005ec8bc0000000ccc0000000000bde7901a59a3102c8ff21d16a0bf25bb203126411063e2f49c080000002f2899c52655c27aa2180ce1194858a405c873d11d98b4a9622123b9c3c96842d39114588cc50d3e4972c6e21653c494e051864c3af931cf3800017022383b23931c380000848cc45ba2640000002110000000781217800000067e0e69d9838e94d2c100a87046c13ba1fa800000e433000107077e20600006e80002cc0820000000257060516400011a86ec00052427d9c5513c2511789620d0a2a42be8da00003c52230f18a562c03f0095442c0003f61d3492200002006f4dbc4a03768a3c6c05030008ecca0c0e54358ea400000000000000001881c712491822954848500000000000237800000018c83ccba20000010000d8c42c0600ae10fe7ad00b8000a6e0003452038da22133021ea457852509b0a8084c354418247c00000000000000000003fb951800000013d0db8c8000018896e839601f3a58b500000000558fad15a7341dc84e03fe32d230090c0000000000000000000040000000000038c800097e8ce1b186782d60cb0000000c9e5d828286d505643327c05fc558762191154017a5e628c213446074530780848704b226f8000fc63f74009fd08b872d0b020b888a41d48619e4bf40000001dec3c8000000055c00000000008d021490744d89141e294302d9e08e2e915329a2c11c62713591b28a5c1c1080000106613f3b703b4e4000028a1a880005a21a28000c1400020517f899806b000000126a90207c921423c1300000000ac88a10738fa1176260273903400014d00018dd2422960289a0c0008a32c500000de2093d8a31c00041a3068000b1a39c14d045125654c31982a00001f236b008c68200009417cc00000000000006c261d2b102c0bce19805c138514e41c13a9b8c7bc4503840ea85f035611307e42d487e04e800008e0000708000066
  | 15 => 0x83270519104ad200000010440002d5000196c3b46012db15247f61630be81cc8804692629e0c91040f258800035e86700000005740001d10c040000002039efcf6a00000000006a23a100015ac0000000001e680002a10000354eb600000013a00000000000fe0cb086c3440000e9840920d800007c51a0988000c4600000000010e8000324a308eae7ed0860f90a689222608000b8033d0a8231914a680095882c4d453e4229b48a622ed1a51a9c7d417b3ea800082076b0ad95ecdd03c2000046857c112000193527a6820918c783807473a306742a66ab06d90dc15203c0000e406b622700000007ac00024a13f90784ed36289900005b90e49a18c8e220494917858e3b41f7837cbb64dc0420654c2c21749d201909e9144578de45f647d00022005bc33e3cb1cc831a1b03581008fa093f2f21dc0ba43b624586c8e4e00000009480004723dd849c77e8ee00022d849094f3d380010ca3571df0ff00708f20000000ba800010e00008f800032199fc7c01851fd00000003e93292074428000391862c0008ea050000000057e1a80de0cce90a0000000000054288171c9e869949e19bc1d061a0000c7505e3b73c51864f2a12c1d58000000000010160000000013300011087b0325800000000018797d406e934293178000000c2bc0000b6a000225800000075c0c4a3e091e8f127ca2a4e3a8131d78a0912e91a056052827a1f423f978449e3331a18000d90367102a40c32c8be4899dfce6a38934b87a8e564280b880004446562a00000cc02af22a800000000049996b906400033981d4f7852836e8000f8084b2568d3062a00030e148d0e24e3090800000017a00c9e3caf84480000fb40004781fa0a6c4e4000000000000060e40d86c40000002221b70fa428d00000000000004251bc05d27aa0db8000a5400008680010f680706514080c848231e84f823e7c600016a8fd67680001848e840003f093409b400021e150cb700000000001032000000000107e3bd11c17101d43f00000a5d2580af2ad927009e85b20c1a50e761153f280003564132b309dc00079149204b4d706a606324e0a241f50000e487b415d2c711685b41e209922ccbac00036701b0eec07f00000000008593fd02f0c180004ab12f12306f204da384000000000013000000039c00000000b20000bc000015f0000aac6541b80001ef80226213960000af400000024a05661d13a21fd49ba43e03f00004464bb49b8c7c7487ef0528f603f03a524f00004a800008291a845090401903bc70807000ea3683d269618c00008ec0a701299a882e76c2218000970000000061c00030936f800094e058000020ca52000000168000000000000000000000001a2c0000000000da90d214b33b8a2c3660b716f8cf0000000186800042200000000010be0000000000ece75510f
  | 16 => 0x88c000185400038c28f000109000006613c090c53900000010c67520000daceca00019f955089400015d85dccec6242fc2098466000036a5380004360000ddc000093000252829e0b514e80007640000280000fe68ba3e58ce8ec2468181a2285fc5482c39a600001e817185540b20004658088c682880001b907c258328987b8000000000236491a1093f200b0b9c3730ea15543b67db1c68ce46a46c03cc803400043b28e0f2468486a43e9ba80004b007a8f20c5e08d1fb07dcbba40e486800080858c28c8eb00000001541ad0a184e9071803c000000000042c000729422000000000037716fc0008871711da46da2013db1778cf02653e783ac9544f61f3892c8c626c0e4207c6a665e35b202000035d0be0ac080a7ab37a1c6800069137618fc000000142800098000000013f000000000000000003a64139d4000000000000006aa4250000c50c4a0000a28000eda0a132e82250f8294489190400054749c8dbc25400000000005726b300000002f2340000070c0001d010d0690ff26e21a7978c24a3b10001bf45fe4750001ff08a60080a080011b81eb1ba81e8ae28f62cf00bc8d87e90b31f288f474e4aa9c2d2b05cf1b106d01e02ef00024192a888539788788b66e01169938b601e317b82d0c9400004f95640f80c522fa1e4fba1483e0800084200000000d035827e08d9328a7a7401018cc43a68153a890d4caa834000023c00045d0002274b942440f28b74d866d4000236c0006022398000a66432151958099c000012234035a94704800a021c000097a3a09ca6a438e00000000000000214adc4a92b624a80ae00000017d000083113718b000044744e0e603946f515b000000063c19c0000f421640218a1ca0238300001a000020f1b30000cd200000007b4000000083000051263900016900000000001e88d920942c300004b82460d185b00001780000774f8a225000000000000031b02d889840b3fb09c000000022b00d40005210511644be0000477a3dc6ec00034980000000000000000b3823226218ad0461913ec9fa00c47b20dca1b800091d11f80000245eb40593884920001871a804bc00000004448ca6af17a80000000002d9818000091e342254c934000148800112604a00000009aa7184249a48b980000f3825cfa644900002ec0008830001adc000026352959c02c0000ac00000002c5366800124c9050001d8000065912b925925c9512f50000da01a8043962c9b00002ff8ee000042744415cd1c04f100000000166f736b94e8af22d93bc87bd1fc63038a186ce2c603197800094a7df23f05b8000000158814c1b81e00002130fcc00013e80000005d73ed000028e627000214879678b2498dc83ec83b00011c4c520000ae00c06f48b11ff8254ce469f0db0ba12a00924ab92042da63520b040879
  | 17 => 0x1b24b600
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe5098c1000e5c5098c100065e6558c100065d6558c100069e6458c100069d6458c100065e7558c100065d7558c100065f5458c100065d5458c10004df7258c1000e5e5058c1000e5c5058c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c10004fa7018c100047f76d4c100047d76d4c100063e64d4c100063d64d4c100065e63d4c100065d63d4c100047f7654c100047d7654c100063e6454c100063d6454c100065e6354c100065d6354c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d88100047e75988100047d7598810004de7398810004dd7398810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e75988100066d75988100066f54988100066d5498810006ce7398810006cd73988100066f53988100066d539881000e6e509881000e6c50988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066e75588100066d75588100066f54588100066d5458810006ce7358810006cd73588100066f53588100066d535881000e6e505881000e6c50588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa70188100047f76d48100047d76d48100053d74d48100063e64d48100063d64d48100065e63d48100065d63d48100066e62d48100066d62d48100047f76548100047d76548100063e64548100063d64548100065e63548100065d63548100066e62548100066d6254810004df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc810006ce62cc810006cd62cc810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c810006ce624c810006cd624c8100047e75984100047d7598410004be7498410004bd74984100047d76d44100063e64d44100063d64d44100055d73d44100065e63d44100065d63d44100066e62d44100066d62d44100047f76544100063e64544100063d64544100065e63544100065d63544100066e62544100066d6254410006766154410004bd76d04100063e65d04100063d65d04100069e63d04100069d63d0410006ae62d0410006ad62d0410004bf76504100063e65504100063d65504100069e63504100069d6350410006ae6250410006ad6250410006b6615041000c7f759801000c7c75980100067565c4010006b564c4010006d563c4010006e562c4010004f97684010006d96384010006e96284010004f77644010006756544010006b56444010006d56344010006e56244010004fb7644010006d96344010006e96244010
  | 1 => 0x451000757325451000755325451000773705451000d7470545100077070545100063f65d05100063c65d05100069f63d05100069c63d05100073551d0510005757590510005b57490510006d463905100063f65505100063c65505100069f63505100069c6350510007375150510007355150510004f47650510005757550510007375450510007355450510006d46350510006b77650510006b47650510007367550510007357550510007376550510007346550510007976350510006b66350510006b46350510007946350510006946350510007375350510007355350510006b76250510006b56250510007375250510007355250510007973250510007953250510007b37050510007b0705051000575758c510005b5748c510006d4638c51000755538c510004f4764c51000575754c510005757588510005b57488510004f47648510005757548510007c532485100047e76941100065f63941100065c63941100073541941100047e76141100053d74141100055d73141100065f63141100065c63141100056d7214110005757114110007354114110006d8638c11000771518c110007b1418c110007d2318c110004f8764c11000759534c11000771514c110007b1414c110007d1314c110007715188110007b14188110004f87648110007695248110007c93248110007715148110007b14148110007e121481100077151c4110007b141c411000d777584110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d76994100047d74994100047d73994100047d729941000c7e70994100047f74594100047f73594100047f72594100047f71594100047d715941000c7c70594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004f671194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d90100047e75990100047d7599010004bd76990100063e65990100063d65990100063e75990100063d759901000e3e509901000e3c50990100063e65590100063d65590100063e75590100063d7559010004bf7159010004bd715901000e3e505901000e3c50590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047f76d50100047d76d50100063e64d50100063d64d50100047f76550100047d76550100063e64550100063d64550100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c100047e7598c100047d7598c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100065e7598c100065d7598c100065f5498c100065d5498c10004dd7298c1000e5
  | 2 => 0x4bc7458a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a1000c7e76d4a1000c7c76d4a100053d74d4a1000c7e7654a1000c7c7654a100066e6254a100066d6254a100065f65cca100065c65cca100065f654ca100065c654ca10006ce624ca10006cd624ca100055d73d461000d7a70d461000d7870546100063f65d06100063c65d06100063f65506100063c655061000759534c210007695248210007c9324821000e7765c42100047d74d95100047d73d95100047d72d95100047e7599510004de7399510004dd7399510004df7359510004dc7359510004be7419510004bd74195100047e76195100053d74195100063e74195100047d74195100063d74195100043d74195100047d73195100047d721951000675711951000c7e701951000c7c70195100047e75991100047d7599110004de7399110004dd73991100047f75591100047c7559110004df7359110004dc7359110004ef7259110004ec72591100047e75191100047d75191100047e76d51100047c76d51100057571d51100047e76551100047c76551100063e64551100063d64551100065f65d8d100065c65d8d100065f75d8d100065c75d8d100065f54d8d100065d54d8d10004dd72d8d100047e7598d100047d7598d10004de7398d100047f7558d100047c7558d100047e7518d100047d7518d10004be7418d10004bd7418d10004ee7218d10004ed7218d10004de7618d100065f6518d100065c6518d10005cd7218d100065e7518d100065d7518d100069e7418d100069d7418d100065f5418d100065d5418d10006ce7218d10004dd7218d10006cd7218d10004cd7218d10006d57118d10006d97018d100047e76d4d100047c76d4d100065f63d4d100065c63d4d100057571d4d100047e7654d100047c7654d100065f6354d100065c6354d100047e75989100047d7598910004de7398910004dd73989100047f75589100047c7558910004bf7458910004bc7458910004df7358910004dc73589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd73189100047e76d49100047c76d49100053d74d49100065f63d49100065c63d49100057571d49100047e76549100047c76549100065f63549100065c6354910004de76cc910004dc76cc9100065f65cc9100065c65cc910004de764c910004dc764c9100065f654c9100065c654c910006ce624c910006cd624c9100047e76d45100055d73d45100065f63d45100065c63d45100057a70d4510005757594510006746594510005b574945100047c76545100065f63545100065c6354510005787054510004f4765451000677765451000674765451000474765451000577745451000577735451000757635451000754635451000577725
  | 3 => 0xd64d4f100057571d4f100047f7654f100047d7654f100063e6454f100063d6454f100065f6354f100065c6354f100047e75d8b100047d75d8b10004be74d8b10004bd74d8b100047e7598b100047d7598b10004de7398b10004dd7398b100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b100047f76d4b100047d76d4b100053d74d4b100063e64d4b100063d64d4b100057571d4b100047f7654b100047d7654b100063e6454b100063d6454b100065e65ccb100065d65ccb100069e64ccb100069d64ccb100065e654cb100065d654cb100069e644cb100069d644cb10006ce624cb10006cd624cb100063e64d47100063d64d47100055d73d4710005b574947100063e64547100063d645471000676655471000577765471000677765471000577745471000736645471000735645471000577735471000577725471000757325471000755325471000d7470547100063e65d07100063d65d07100073551d07100057575907100063e65507100063d6550710007375150710007355150710005757550710006b66450710007375450710007355450710005b77650710006b77650710007367550710007357550710007366550710007356550710006b66350710006b46350710007375350710007355350710006b76250710006b5625071000737525071000735525071000797325071000795325071000575758c710005b5748c71000755538c71000575754c710005757588710005b57488710006b56488710005757548710006b56448710007c532487100063e64943100063d64943100073541943100053d74143100063e64143100063d64143100055d73143100056d72143100057571143100073541143100047d74d96100047d73d96100047d72d961000e7571d961000e7a70d9610004be7419610004bd7419610004de7319610004dd7319610004ee7219610004ed721961000e3e74196100047d741961000e3d74196100043d741961000e5e73196100047d731961000e5d73196100045d731961000e6e72196100047d721961000e6d72196100046d721961000e75711961000e7a70196100047e75992100047d75992100047f75592100047c75592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed721921000c7e76d521000c7c76d521000c7e765521000c7c76552100063e64552100063d64552100047e7598e100047d7598e100047f7558e100047c7558e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e1000c7e76d4e1000c7c76d4e1000c7e7654e1000c7c7654e100065e6354e100065d6354e100047e7598a100047d7598a10004de7398a10004dd7398a100047f7558a100047c7558a10004bf7458a10
  | 4 => 0x48200047f76548200063e64548200063d64548200065e63548200065d63548200066e6254820004dd76cc8200065e65cc8200065d65cc8200069e64cc8200069d64cc820004df764c8200065e654c8200065d654c8200069e644c8200069d644c820006ce624c8200047e75984200047d7598420004be7498420004bd7498420006766598420006756598420006b66498420006b56498420006d66398420006d56398420006767598420006757598420006b67498420006b57498420006775498420006755498420006775398420006755398420006775298420006755298420006d73298420006d5329842000e76509842000e745098420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006767558420006757558420006b67458420006b57458420006775458420006755458420006775358420006755358420006775258420006755258420006d73258420006d5325842000e76505842000e7450584200047f76d44200047d76d44200063e64d44200063d64d44200055d73d44200065e63d44200065d63d44200067661d44200067561d44200047f76544200047d76544200063e64544200063d64544200065e63544200065d6354420006766154420006756154420004bf76d0420004bd76d04200063e65d04200063d65d04200069e63d04200069d63d0420006b661d0420006b561d0420004bf7650420004bd76504200063e65504200063d65504200069e63504200069d6350420006b66150420006b5615042000c7f759802000c7c75980200066d65c8020006ad64c8020006cd63c8020006e561c8020006b96488020006f16188020004ef76480200066d6548020006ad6448020006cd6348020006e56148020004fb7648020006b96448020006f16148020004be74d9710004bd74d9710004de7399710004dd73997100055d73997100047d74997100065e73997100047d73997100065d73997100045d73997100047d72997100067671997100047f74597100047f73597100047f7259710004be7419710004bd74197100047e75d93100047d75d93100047e75993100047d7599310004de7399310004dd73993100063e65993100063d65993100063e75993100063d75993100069e73993100069d7399310006b671993100063e65593100063d65593100063e75593100063d75593100047e75193100047d75193100047f76d53100047d76d53100063e64d53100063d64d53100057571d53100047f76553100047d76553100063e64553100063d64553100047e75d8f100047d75d8f10004be74d8f10004bd74d8f100047e7598f100047d7598f100047e7518f100047d7518f10004be7418f10004bd7418f10004ee7218f10004ed7218f100047f76d4f100047d76d4f100063e64d4f100063
  | 5 => 0x47e76545200047c76545200063f64545200063c64545200074d3254520004be76d0520004bc76d05200063f65d05200063c65d05200072d52d05200078d32d0520004be7650520004bc76505200063f65505200063c65505200072d52505200078d32505200056d75c8520005cd73c85200056d7548520007a541485200047e76941200063f64941200063c64941200074d32941200047e76141200053d74141200063f64141200063c64141200055d73141200056d72141200074d3214120005757114120006b86490120007695290120007aa4290120007c93290120004f87650120007395450120007695250120007a94250120007c932501200076952c8120007c932c812000d6f7588120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d76994200047d74994200047d73994200047d719942000c7e70994200047f74594200047f73594200047f72594200047d72594200047f715942000c7c70594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004ee7219420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d90200047e75990200047d7599020004bd76990200063e65990200063d65990200063e75990200063d7599020004bd719902000e3e509902000e3c50990200063e65590200063d65590200063e75590200063d7559020004bf715902000e3e505902000e3c50590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f57119020004fa70190200047f76d50200047d76d50200063e64d50200063d64d50200047f76550200047d76550200063e64550200063d64550200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c200047e7598c200047d7598c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c200065e7598c200065d7598c200065f5498c200065d5498c2000e5e5098c2000e5c5098c200065e6558c200065d6558c200069e6458c200069d6458c200065e7558c200065d7558c200065f5458c200065d5458c20004df7258c20004dd7258c2000e5e5058c2000e5c5058c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c200047f76d4c200047d76d4c200063e64d4c200063d64d4c200065e63d4c200065d63d4c200047f7654c200047d7654c200063e6454c200063d6454c200065e6354c200065d6354c200047e75988200047d7598820004de7398820004dd73988200047d76d48200053d74d48200063e64d48200063d64d48200065e63d48200065d63d
  | 6 => 0xd73d462000c7c76546200067661546200067561546200063f65d06200063c65d06200063f65506200063c6550620006b66150620006b5615062000739545022000e6f65c82200047d74d95200047d73d95200047d71d95200047e7599520004be7499520004bd7499520004bf7459520004bc7459520004de7319520004dd73195200047e76195200055d73195200047d74195200065e73195200047d73195200065d73195200045d73195200066d72195200047d71195200063f65d91200063c65d91200063f75d91200063c75d9120004bd71d91200047e75991200047d7599120004be74991200047f75591200047c75591200047e75191200047d7519120004de7319120004dd7319120004f67119120004f57119120004be76191200063f65191200063c6519120005b571191200063e75191200063d75191200069e73191200069d7319120006ad7219120006b67119120004bd7119120006b57119120004b57119120006b970191200047e76d51200047c76d51200063f64d51200063c64d51200056d72d51200047e76551200047c76551200063f64551200063c64551200047e7598d200047d7598d20004be7498d20004bd7498d200047f7558d200047c7558d20004bf7458d20004bc7458d20004f77158d20004f47158d200047e7518d200047d7518d200047e76d4d200047c76d4d200063f64d4d200063c64d4d200056d72d4d200047e7654d200047c7654d200063f6454d200063c6454d200065e6354d200065d6354d200047e76d49200053d74d49200063f64d49200063c64d49200057a70d49200056d75949200066c6594920005cd73949200047c76549200063f64549200063c6454920005787054920004ec76549200066f76549200066c76549200046c76549200056f74549200072f64549200072c64549200056f73549200056f71549200076b705492000d6c70549200076870549200056d7590920006ac64909200072d5490920005cd7390920004ec76509200056d75509200065f65cc9200065c65cc9200069f64cc9200069c64cc9200074d52cc9200056d758c920006ac648c920005cd738c9200065f654c9200065c654c9200069f644c9200069c644c9200074f524c9200074d524c920004ec764c9200056d754c920006ac644c9200074f534c9200074d534c920006cf764c920006cc764c9200074e754c9200074d754c9200074f654c9200074c654c9200078f644c920006ce644c920006cc644c9200078c644c9200068c644c9200074f544c9200074d544c920007cb704c920007c8704c920006cd32d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd73185200047e76d45200047c76d45200063f64d45200063c64d45200055d73d45200056d72d45200074d32d4520
  | 7 => 0x8f200047f76d4f200047d76d4f200065e63d4f200065d63d4f200056d72d4f200047f7654f200047d7654f200065e6354f200065d6354f200053d74d4b200065e63d4b200065d63d4b20005cd7394b200065e6354b200065d6354b200066e6554b200056f7654b200066f7654b200056f7454b200056f7354b200074e6354b200074d6354b200056f7154b2000d6c7054b200056d7590b200072d5490b20005cd7390b200056d7550b200065e65ccb200065d65ccb200074d52ccb200056d758cb200065e654cb200065d654cb200074f524cb200074d524cb200056d754cb20006ce634cb200074f534cb200074d534cb20005cf764cb20006cf764cb200074e754cb200074d754cb200074e654cb200074d654cb20006ce644cb20006cc644cb200074f544cb200074d544cb200047e75987200047d7598720004be7498720004bd7498720006cd32587200047f76d47200047d76d47200055d73d47200065e63d47200065d63d47200056d72d47200074d32d47200047f76547200047d76547200065e63547200065d63547200074d32547200063e65d07200063d65d07200069e63d07200069d63d07200072d52d07200078d32d07200063e65507200063d65507200069e63507200069d63507200072d52507200078d3250720006b66150720006b561507200056d75c8720005cd73c8720006cd63c87200056d7548720006cd6348720007a541487200065e63943200065d63943200074d32943200053d74143200055d73143200065e63143200065d63143200056d72143200074d32143200057571143200047d74d96200047d73d962000e6d72d96200047d71d962000e7a70d9620004be7419620004bd7419620004de7319620004dd7319620004f67119620004f5711962000e3e74196200047d741962000e3d74196200043d741962000e5e73196200047d731962000e5d73196200045d731962000e6d721962000e7671196200047d711962000e75711962000475711962000e7a70196200047e75992200047d75992200047f75592200047c75592200047e75192200047d7519220004de7319220004dd7319220004f67119220004f5711922000c7e76d522000c7c76d522000c7e765522000c7c76552200063e64552200063d64552200047e7598e200047d7598e200047f7558e200047c7558e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e2000c7e76d4e2000c7c76d4e2000c7e7654e2000c7c7654e200065e6354e200065d6354e200053d74d4a2000d7a70d4a2000d787054a200065f65cca200065c65cca200065f654ca200065c654ca200047e75986200047d7598620004be7498620004bd74986200047f75586200047c7558620004df7358620004dc735862000c7e76d46200055
  | 8 => 0x69e64cc8300069d64cc830006cd62cc8300065e654c8300065d654c8300069e644c8300069d644c830006ce624c8300047e75984300047d7598430004be7498430004bd7498430006766598430006756598430006b66498430006b56498430006e66298430006e56298430006767598430006757598430006b67498430006b57498430006775498430006755498430006775398430006755398430006775298430006755298430006d73298430006d5329843000e76509843000e745098430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006767558430006757558430006b67458430006b57458430006775458430006755458430006775358430006755358430006775258430006755258430006d73258430006d5325843000e76505843000e7450584300047f76d44300047d76d44300063e64d44300063d64d44300055d73d44300066e62d44300066d62d44300067661d44300067561d44300047f76544300047d76544300063e64544300063d64544300055f73544300066e62544300066d6254430006766154430006756154430004bf76d0430004bd76d04300063e65d04300063d65d0430006ae62d0430006ad62d0430006b661d0430006b561d0430004bf7650430004bd76504300063e65504300063d6550430006ae6250430006ad6250430006b66150430006b56150430004dd768c4300065d658c4300069d648c430006cd628c430006d5618c4300065d650c4300069d640c430005cd720c430006cd620c430006d5610c43000795410c430005d9700c43000c7f759803000c7c75980300065d65cc0300069d64cc030006cd62cc030006d561cc030006f1618c030004df764c0300065d654c0300069d644c030006cd624c030006d5614c030004fb764c030006f1614c030004de73d9720004dd73d9720004be7499720004bd74997200053d74997200063e74997200047d74997200063d74997200043d74997200047d73997200066e72997200047d71997200047f74597200047f73597200047f7159720004de7319720004dd73197200047e75d93200047d75d9320004de73d9320004dd73d93200047e75993200047d75993200047e75193200047d7519320004de7319320004dd7319320004f67119320004f571193200047f76d53200047d76d53200056d72d53200047f76553200047d76553200063f64553200063c64553200047e75d8f200047d75d8f200047e7598f200047d7598f20004be7498f20004bd7498f200065e6598f200065d6598f200065e7598f200065d7598f200069e7498f200069d7498f200065f5498f200065d5498f20006ce7298f200065e6558f200065d6558f200065e7558f200065d7558f200065f5458f200065d5458f200047e7518f200047d751
  | 9 => 0xb7054d3000d5c7054d30007587054d300055d7590d30005cd7290d30004dc7650d300055d7550d300065d53d89300047e75189300047d75189300047e76d49300047c76d49300053d74d49300055d73d49300047e76549300047c76549300055d75cc9300065f65cc9300065c65cc9300059d74cc9300055d754c9300065f654c9300065c654c930006cf624c9300047e75185300047d7518530004be7418530004bd74185300065d5318530004ee7218530004ed72185300047e76d45300047c76d45300055d73d45300047e76545300047c76545300063f65d05300063c65d05300071d53d05300063f65505300063c65505300071d5350530006b76150530006b46150530004de76cc5300055d75cc5300079541cc5300055d754c5300047e76941300047e76141300053d74141300055d73141300056d72141300057571141300075953cc13000d5f758c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300047d74994300047d72994300047d719943000c7e70994300047f74594300047f73594300047d73594300047f72594300047f715943000c7c70594300047e7519430004be7419430004bd7419430004de7319430004ee7219430004ed7219430004f67119430004f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d90300047e75990300047d7599030004bd76990300063e65990300063d65990300063e75990300063d7599030004bd719903000e3e509903000e3c50990300063e65590300063d65590300063e75590300063d7559030004bf715903000e3e505903000e3c50590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f571190300047f76d50300047d76d50300063e64d50300063d64d50300047f76550300047d76550300063e64550300063d64550300047e7598c300047d7598c300047d76d4c300063e64d4c300063d64d4c300047f7654c300063e6454c300063d6454c300065e6354c300047e75988300047d75988300066e65988300066d6598830006ae6498830006ad64988300066e75988300066d75988300066f54988300066d54988300066f53988300066d539883000e6e509883000e6c50988300066e65588300066d6558830006ae6458830006ad64588300066e75588300066d75588300066f54588300066d5458830006ce73588300066f53588300066d535883000e6e505883000e6c50588300047f76d48300047d76d48300053d74d48300063e64d48300063d64d48300066e62d48300066d62d48300047f76548300047d76548300063e64548300063d64548300066e62548300066d62548300065e65cc8300065d65cc830
  | 10 => 0x53300047d76553300065e6554f300055f7654f300065f7654f300055f7454f300055f7254f300055f7154f3000d5c7054f300055d7590f30005cd7290f300055d7550f300047e7598b300047d7598b300065d5358b300047f76d4b300047d76d4b300053d74d4b300055d73d4b300047f7654b300047d7654b300055d75ccb300065e65ccb300065d65ccb300059d74ccb30006cd62ccb300055d754cb300065e654cb300065d654cb300047e75987300047d7598730004be7498730004bd74987300065d53987300047f76d47300047d76d47300055d73d47300047f76547300047d76547300063e65d07300063d65d07300071d53d07300063e65507300063d65507300071d53507300055d75cc7300079541cc7300055d754c7300053d74143300055d73143300056d72143300057571143300047d74d963000e5d73d96300047d72d96300047d71d963000e7a70d9630004be7419630004bd7419630004ee7219630004ed7219630004f67119630004f5711963000e3e74196300047d741963000e3d74196300043d741963000e5d731963000e6e72196300047d721963000e6d72196300046d721963000e7671196300047d711963000e75711963000475711963000e7a70196300047e75992300047d75992300047f75592300047c75592300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f5711923000c7e76d523000c7c76d523000c7e765523000c7c76552300063e64552300063d645523000d7a70d4e3000d787054e300047e7598a300047d7598a300047f7558a300047c7558a30004bf7458a30004bc7458a3000c7e76d4a300053d74d4a3000c7c7654a300066e6254a300066d6254a300065f65cca300065c65cca300065f654ca300065c654ca30006ce624ca30006cd624ca300047e75986300047d7598630004be7498630004bd74986300047f75586300047c755863000c7e76d46300055d73d463000c7c76546300055f73546300067661546300067561546300063f65d06300063c65d06300063f65506300063c6550630006b66150630006b561506300065f658c6300065f650c630005cd720c63000795410c630005d9700c63000e5f65cc2300047d74d95300047d72d95300047d71d95300047e75995300047e76195300047d74195300065d73195300047d72195300047d71195300047e75991300047d7599130004f67199130004f571991300047f75591300047c75591300047e75191300047d75191300047e76d51300047c76d51300055d73d51300047e76551300047c76551300047e76d4d300057a70d4d300055d7594d300065c6594d300047c7654d30005787054d30004dc7654d300065f7654d300065c7654d300045c7654d300055f7454d300055f7254d300055f7154d300075
  | 11 => 0x66e65988400066d6598840006ce6398840006cd63988400066e75988400066d75988400066f54988400066d5498840006ce7398840006cd73988400066f53988400066d539884000e6e509884000e6c50988400066e65588400066d6558840006ce6358840006cd63588400066e75588400066d75588400066f54588400066d5458840006ce7358840006cd73588400066f53588400066d535884000e6e505884000e6c50588400047f76d48400047d76d48400053d74d48400065e63d48400065d63d48400066e62d48400066d62d48400047f76548400047d76548400053f74548400065e63548400065d63548400066e62548400066d6254840004bd76908400063d65908400069d6390840006ad62908400063d65108400069d6310840006ad6210840005b57110840005b97010840004df76cc840004dd76cc8400065e65cc8400065d65cc840006ce62cc840006cd62cc840004df764c840004dd764c8400065e654c8400065d654c840006ce624c840006cd624c8400078c424c8400047e75984400047d7598440006766598440006756598440006d66398440006d56398440006e66298440006e56298440006767598440006757598440006775498440006755498440006775398440006755398440006775298440006755298440006d73298440006d5329844000e76509844000e745098440006766558440006756558440006d66358440006d56358440006e66258440006e56258440006767558440006757558440006b67458440006775458440006755458440006775358440006755358440006775258440006755258440006b64258440006b44258440006d73258440006d5325844000e76505844000e7450584400047f76d44400047d76d44400055d73d44400065e63d44400065d63d44400066e62d44400066d62d44400067661d44400067561d44400047f76544400047d76544400065e63544400065d63544400066e62544400066d62544400067661544400067561544400063e65d04400063d65d04400069e63d04400069d63d0440006ae62d0440006ad62d0440006b561d04400063e65504400063d65504400069e63504400069d6350440006ae6250440006ad6250440006b6615044000c7f759804000c7c75980400063d65d00400069d63d0040006ad62d0040006b561d0040006e96290040004bf76500400063d65500400069d6350040006ad6250040006b56150040004fb7650040006e962500400047d74997300065e73997300047d72997300047d71997300047f74597300047f72597300047f71597300047e75d93300047d75d9330004ee72d9330004ed72d93300047e75993300047d7599330004f67199330004f571993300047e75193300047d75193300047f76d53300047d76d53300055d73d53300047f765
  | 12 => 0xf654ca400065c654ca40006ce624ca40006cd624ca400078c424ca400047e75986400047d75986400047f75586400047c7558640004df7358640004dc735864000c7e76d46400055d73d464000c7c76546400067661546400067561546400063f65d06400063c65d06400063f65506400063c6550640006b66150640006b5615064000e3f65d024000f3a50d02400073954d02400047d73d95400047d72d95400047d71d95400047e75995400047e76195400063d74195400047d73195400047d72195400047d71195400047e76d51400057a70d51400053d75951400063c65951400047c7655140005787055140004bc76551400063f76551400063c76551400043c76551400053f73551400053f72551400053f71551400073b705514000d3c70551400073870551400047e7518d400047d7518d400047e76d4d400047c76d4d400053d74d4d400047e7654d400047c7654d400053d75d0d40005b571d0d400053d7550d400047e75189400047d75189400063d5418940004de7318940004dd7318940004f67118940004f571189400047e76d49400047c76d49400053d74d49400047e76549400047c7654940004be76d09400053d75d09400053d75509400065f65cc9400065c65cc9400071d54cc9400065f654c9400065c654c9400071d544c940006cf624c940006cc624c9400078f424c9400063d54d85400047e75185400047d75185400047e76d45400047c76d45400053d74d45400055d73d45400047e76545400047c76545400053d75d05400063f65d05400063c65d05400059d73d05400053d75505400063f65505400063c6550540006b761505400047e76941400047e76141400053d74141400055d73141400056d72141400057571141400073954d014000d3f7590140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d76994400047d73994400047d72994400047d719944000c7e70994400047f74594400047d74594400047f73594400047f72594400047f715944000c7c70594400047e7519440004be7419440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f571194400047e75990400047d75990400047d76d50400047f76550400063e64550400047e7598c400047d7598c400065e6598c400065d6598c400065e7598c400065d7598c400065f5498c400065d5498c40004dd7298c4000e5e5098c4000e5c5098c400065e6558c400065d6558c400065e7558c400065d7558c400065f5458c400065d5458c40004df7258c4000e5e5058c4000e5c5058c400047f76d4c400047d76d4c400065e63d4c400065d63d4c400047f7654c400047d7654c400065e6354c400065d6354c400047e75988400047d7598840004de7398840004dd7398840
  | 13 => 0x84500055d73c84500065d63c84500066d62c84500074d32c84500067561c845000c7e76884500047d76884500053e74884500053d74884500063d64884500065d63884500066d62884500067561884500073541884500047d76484500063d64484500065d63484500066d62484500074d324845000675614845000735414845000c7e76084500047d76084500053e74084500053d74084500063d64084500055e73084500055d73084500065d63084500066d620845000675610845000d7a70084500057970084500065f32980500065d32980500063f41980500063d419805000e7a709805000f3a649805000f39649805000f5a639805000f59639805000f6a629805000f6962980500075b329805000759329805000f72619805000f7161980500073b41980500073941980500063e74997400047d73997400047d72997400047d71997400047f73597400047f72597400047f71597400063e65953400063e65553400053f76553400063f76553400053f73553400053f72553400053f715534000d3c70553400047e7598f400047d7598f40004ee7298f40004ed7298f400047f76d4f400047d76d4f400053d74d4f400047f7654f400047d7654f400053d75d0f40005b571d0f400053d7550f400047e7598b400047d7598b400063d5498b40004de7398b40004dd7398b400047f76d4b400047d76d4b400053d74d4b400047f7654b400047d7654b400053d75d0b400053d7550b400065e65ccb400065d65ccb400071d54ccb400065e654cb400065d654cb400071d544cb400078f424cb400047e75987400047d75987400063d54587400047f76d47400047d76d47400053d74d47400055d73d47400047f76547400047d76547400053d75d07400063e65d07400063d65d07400059d73d0740006b561d07400053d75507400063e65507400063d65507400053d74143400055d73143400056d721434000575711434000e3d74d96400047d73d96400047d72d96400047d71d964000e7a70d9640004de7319640004dd7319640004ee7219640004ed7219640004f67119640004f5711964000e3d741964000e5e73196400047d731964000e5d73196400045d731964000e6e72196400047d721964000e6d72196400046d721964000e7671196400047d711964000e75711964000475711964000e7a701964000d7a70d524000d7870552400047e7598e400047d7598e400047f7558e400047c7558e4000c7e76d4e4000c7c7654e400065e6354e400065d6354e400047e7598a400047d7598a40004de7398a40004dd7398a400047f7558a400047c7558a4000c7e76d4a400053d74d4a4000c7c7654a400053f7454a400066e6254a400066d6254a400063f6590a400063f6510a40005b57110a40005b97010a400065f65cca400065c65cca400065
  | 14 => 0x677765845000736745845000735745845000e77645845000676645845000f36645845000636645845000675645845000f35645845000635645845000e74645845000e77635845000676635845000f56635845000656635845000675635845000f55635845000655635845000e74635845000e77625845000676625845000f66625845000666625845000675625845000f65625845000665625845000e74625845000757325845000755325845000e76605845000677745845000676745845000636745845000675745845000635745845000674745845000677735845000676735845000675735845000674735845000677435845000676435845000675435845000674435845000677725845000676725845000675725845000674725845000677425845000676425845000675425845000674425845000677325845000657325845000676325845000675325845000655325845000674325845000e76705845000e74705845000e76405845000e74405845000e76305845000e74305845000e76205845000e74205845000c7e76d04500047d76d04500063d64d04500055e73d04500055d73d04500065d63d04500066d62d04500067561d04500053f76d04500063e76d04500053d76d04500063d76d04500043d76d04500071e73d04500071d73d04500071e63d04500063d63d04500071d63d04500061d63d04500072e62d04500063d62d04500072d62d04500062d62d04500071f32d04500071d32d04500073661d04500063d61d04500073561d04500063561d045000c7e76904500047d76904500053d74904500063d64904500065d63904500066d62904500067561904500047d76504500063d64504500065d63504500066d62504500067561504500053f76504500063e76504500053d76504500063d76504500043d76504500071e63504500063d63504500071d63504500061d63504500072e62504500063d62504500072d62504500062d62504500071f32504500071d32504500073771504500073661504500063d615045000735615045000635615045000c7e76104500047d76104500053e74104500063d64104500065d63104500066d621045000675611045000c7e76cc4500047d76cc4500063d64cc4500065d63cc4500066d62cc4500067561cc4500073541cc45000c7e768c4500047d768c4500053e748c4500053d748c4500063d648c4500065d638c4500066d628c45000675618c4500047d764c4500063d644c4500065d634c4500066d624c45000675614c45000c7e760c4500047d760c4500053e740c4500053d740c4500063d640c4500065d630c4500056e720c4500056d720c4500066d620c45000675610c45000735410c45000d7a700c45000579700c45000c7e76c84500047d76c84500063d64c84500055e73c
  | 15 => 0xf64588500066e645885000f2e64588500062e64588500066d645885000f2d64588500062d645885000e6c64588500074e73588500074d735885000e6f63588500066e635885000f4e63588500064e63588500066d635885000f4d63588500064d635885000e6c635885000e6f615885000e6c615885000e6e60588500066f74588500066e74588500066d74588500066c74588500066f73588500066e73588500064e73588500066d73588500064d73588500066c73588500066f43588500066e43588500066d43588500066c43588500066f71588500066e71588500066d71588500066c715885000e6e705885000e6c705885000e6e405885000e6c405885000e6e305885000e6c305885000e6e105885000e6c105885000c7e76d08500047d76d08500063d64d08500065d63d08500066d62d085000c7e76908500047d76908500063d64908500055e73908500055d73908500065d63908500066d62908500047d76508500063d64508500065d63508500066d625085000c7e76108500047d76108500063d64108500055e73108500055d73108500065d63108500066d621085000576711085000575711085000d7a701085000579701085000c7e76cc8500047d76cc8500053e74cc8500053d74cc8500063d64cc8500065d63cc8500066d62cc8500055f76cc8500065e76cc8500055d76cc8500065d76cc8500045d76cc8500071e74cc8500071d74cc8500071e64cc8500065d64cc8500071d64cc8500061d64cc8500074e62cc8500065d62cc8500074d62cc8500064d62cc85000c7e768c8500047d768c8500063d648c8500055d738c8500065d638c8500066d628c8500047d764c8500063d644c8500065d634c8500066d624c8500055f764c8500065e764c8500055d764c8500065d764c8500045d764c8500071e644c8500065d644c8500071d644c8500061d644c8500074f724c8500074e624c8500065d624c8500074d624c8500064d624c8500074f424c8500074c424c85000c7e760c8500047d760c8500063d640c8500055e730c8500065d630c8500066d620c8500053e74984500053d74984500063d64984500065d63984500066d629845000d75769845000736749845000735749845000e77649845000f36649845000675649845000f35649845000635649845000e77639845000f56639845000675639845000f55639845000655639845000e77629845000f66629845000675629845000f65629845000665629845000757329845000755329845000e7660984500063e64584500063d64584500065e63584500065d63584500066e62584500066d625845000e7461584500047f74584500063e74584500063d74584500047f73584500047f72584500065f32584500065d325845000e76105845000e74105845000d777658450
  | 16 => 0x450004bf7650450004bd76504500069e63504500069d6350450006ae6250450006ad6250450006b66150450006b561504500063d64d40500065d63d40500066d62d40500067561d40500047f76540500063d64540500065d63540500066d6254050006756154050004fb765405000e3f649905000d3d769905000e3f639905000e3f62990500053d719905000e3f619905000e3e609905000e3c64590500047f73590500047f72590500047f715905000e3e405905000e3c405905000d3f76590500063f765905000e3f635905000e3c635905000e3f625905000e3c62590500053f715905000e3f615905000e3c615905000e3e60590500063f73590500063e73590500063d73590500063c73590500063f72590500063e72590500063d72590500063c72590500063f71590500043f71590500063e71590500063d71590500063c715905000e3e705905000e3c705905000e3e305905000e3c305905000e3e205905000e3c205905000e3e105905000e3c10590500063d6498c5000d5d7698c5000e5f6498c5000f1e6498c500065d6498c5000f1d6498c500061d6498c500055d7298c5000e5f6298c5000e5f6198c5000e5e6098c500063e6458c500063d6458c5000e5c6358c500047f7458c500047f7258c500047f7158c5000e5e3058c5000e5c3058c5000d5f7658c500065f7658c5000e5f6458c500065e6458c5000f1e6458c500061e6458c500065d6458c5000f1d6458c500061d6458c5000e5c6458c500055f7258c5000e5f6258c5000e5c6258c5000e5f6158c5000e5c6158c5000e5e6058c500065f7458c500065e7458c500065d7458c500065c7458c500065f7258c500045f7258c500065e7258c500065d7258c500065c7258c500065f7158c500065e7158c500065d7158c500065c7158c5000e5e7058c5000e5c7058c5000e5e4058c5000e5c4058c5000e5e2058c5000e5c2058c5000e5e1058c5000e5c1058c5000c7e76d0c500047d76d0c500063d64d0c500065d63d0c500057671d0c500057571d0c5000c7e7690c500047d7690c500063d6490c500065d6390c500056e7290c500056d7290c500047d7650c500063d6450c500065d6350c5000c7e7610c500047d7610c500063d6410c500065d6310c500063d64988500055e73988500055d73988500065d639885000d6d769885000e6f649885000f2e64988500066d649885000f2d64988500062d64988500074e73988500074d739885000e6f639885000f4e63988500066d639885000f4d63988500064d639885000e6f619885000e6e60988500063e64588500063d64588500065e63588500065d635885000e6c62588500047f74588500047f73588500065e73588500065d73588500047f715885000e6e205885000e6c205885000d6f76588500066f765885000e6
  | 17 => 0xd7a70150500069e6498c500069d6498c500065f5498c500065d5498c50004dd7298c500069e6458c500069d6458c500065e7558c500065f5458c500065e5458c500065d5458c500065c5458c50004df7258c500063e64d4c500063d64d4c500065d63d4c5000d7a70d4c500047d7694c500063d6494c500065d6394c500063e6454c500063d6454c500065e6354c500063d6414c500065d6314c5000d7a7014c50004de7398850004dd7398850006ae6498850006ad6498850006ce6398850006cd63988500066f54988500066d5498850006ce7398850006cd73988500066f53988500066d5398850006ae6458850006ad6458850006ce6358850006cd63588500066e75588500066f54588500066e54588500066d54588500066c5458850006ce7358850006cd73588500066f53588500066e53588500066d53588500066c53588500053e74d48500053d74d48500063e64d48500063d64d48500065e63d48500065d63d48500066d62d485000d7a70d48500047d76948500063d64948500055e73948500055d73948500065d63948500066d62948500063e64548500063d64548500065e63548500065d63548500066e62548500063d64148500055e73148500055d73148500065d63148500066d621485000d7a7014850004df76cc850004dd76cc8500069e64cc8500069d64cc850006ce62cc850006cd62cc850004df764c850004dd764c8500069e644c8500069d644c850006ce624c850006cd624c850004be7498450004bd7498450006b66498450006b56498450006d66398450006d56398450006e66298450006e56298450006b67498450006b57498450006775498450006755498450006775398450006755398450006775298450006755298450006d73298450006d53298450006b66458450006b56458450006d66358450006d56358450006e66258450006e56258450006767558450006b67458450006b57458450006775458450006765458450006755458450006745458450006775358450006765358450006755358450006745358450006775258450006765258450006755258450006745258450006d73258450006d532584500063e64d44500063d64d44500055e73d44500055d73d44500065e63d44500065d63d44500066e62d44500066d62d44500067561d445000d7a70d44500047d76944500053e74944500053d74944500063d64944500065d63944500066d62944500067561944500063e64544500063d64544500065e63544500065d63544500066e62544500066d62544500067661544500053e74144500053d74144500063d64144500065d63144500066d621445000675611445000d7a7014450004bf76d0450004bd76d04500069e63d04500069d63d0450006ae62d0450006ad62d0450006b661d0450006b561d
  | 18 => 0xc7458a500047f7358a500047f7158a5000e6e2058a5000e6c2058a5000c7e76d0a500047d76d0a500063d64d0a5000c7e7690a500047d7690a500055e7390a500055d7390a500066d6290a500047d7650a500063d6450a500066d6250a5000c7e7610a500047d7610a500055e7310a500055d7310a50005767110a50005757110a5000d7a7010a50005797010a5000c7e76cca500047d76cca500053e74cca500053d74cca500065d63cca500065e76cca500065d76cca500071e74cca500071d74cca500065d64cca500065d62cca5000c7e768ca500047d768ca500066d628ca500047d764ca500065d634ca500066d624ca500065e764ca500065d764ca500065d644ca500074f724ca500074e624ca500065d624ca500074d624ca500064d624ca500074f424ca500074c424ca5000c7e760ca500047d760ca500053e74986500053d749865000e7761986500055f73586500055c73586500047f74586500047f73586500065f73586500045f73586500065c73586500047f72586500065f32586500065d325865000e76105865000e74105865000c7e76d06500047d76d06500063d64d06500055e73d06500055d73d06500063e76d06500063d76d06500071e73d06500071d73d06500063d63d06500063d62d06500071f32d06500071d32d06500063d61d065000c7e76906500047d76906500067561906500047d76506500063d64506500067561506500063e76506500063d76506500063d63506500063d62506500071f32506500071d32506500073771506500073661506500063d615065000735615065000635615065000c7e76106500047d761065000c7e76cc6500047d76cc6500065d63cc6500073541cc65000c7e768c6500047d768c6500053e748c6500053d748c65000675618c6500047d764c6500065d634c65000675614c65000c7e760c6500047d760c6500053e740c6500053d740c6500056e720c6500056d720c65000735410c65000d7a700c65000579700c65000c7e76c86500047d76c86500055e73c86500055d73c86500066d62c86500074d32c865000c7e76886500047d76886500053e74886500053d74886500067561886500073541886500047d76486500066d62486500074d324865000675614865000735414865000c7e76086500047d76086500053e74086500053d74086500055e73086500055d730865000d7a70086500057970086500047e76d51500063f64551500047e76d4d500065f6354d50004de7318950004dd73189500047e76d49500053d74d49500066f6254950004be7418550004bd74185500047e76d45500055d73d4550006776154550004bd71990500063e7559050004bf71590500063e64d50500063d64d505000d7a70d50500047d76950500063d64950500063e64550500063d6415050
  | 19 => 0xc8210069e644c8210069d644c821006ce624c8210047e75984210047d7598421004be7498421004bd74984210047d76d44210063e64d44210063d64d44210055d73d44210065e63d44210065d63d44210047f76544210063e64544210063d64544210065e63544210065d6354421004bd76d04210063e65d04210063d65d04210069e63d04210069d63d0421004bf76504210063e65504210063d65504210069e63504210069d6350421006b66150421006cd63c8421006b56488421004ef7648421006cd6348421004f77648421006b564484210067a6598021006796598021006ba6498021006b96498021006da6398021006d9639802100e7b759802100e7875980210067b54980210067954980210067b53980210067953980210067b5298021006795298021006db3298021006d932980210067b5198021006795198021006bb4198021006b941980210047f75580210047c75580210067a6558021006796558021006ba6458021006b96458021006da6358021006d963580210067b75580210067875580210067b54580210067954580210067b53580210067953580210067b5258021006795258021006db3258021006d932580210067b5158021006795158021006bb4158021006b94158021006eb2158021006f22158021006e92158021006f121580210063e64d53500063d64d53500065d63d4f50004de7398b50004dd7398b500053d74d4b500066d62d4b50004be7498750004bd74987500055d73d47500067561d47500063d649525000d7a70952500057970952500063e64552500063d645525000d78705525000d7a7094e500065e6354e500065d6354e5000d787054e50004de7398a50004dd7398a50004bf7458a50004bc7458a500053e74d4a500053d74d4a500055e7394a500055d7394a5000d7a7094a500066e6254a500066d6254a5000d787054a500055e7314a500055d7314a50006ce624ca50006cd624ca50004be7498650004bd7498650004df7358650004dc73586500055e73d46500055d73d46500053e74946500053d749465000d7a709465000676615465000675615465000d7870546500053e74146500053d7414650006b66150650006b5615065000e3f649925000e3c64592500047f73592500047f72592500047f715925000e3e405925000e3c405925000e5f6398e500047f7458e500047f7258e500047f7158e5000e5e3058e5000e5c3058e5000c7e76d0e500047d76d0e500063d64d0e500057671d0e500057571d0e5000c7e7690e500047d7690e500065d6390e500056e7290e500056d7290e500047d7650e500063d6450e500065d6350e5000c7e7610e500047d7610e500055e7398a500055d7398a5000e6f6298a500053f7458a500053c7458a500047f7458a500063f7458a500043f7458a500063
  | 20 => 0x47d76545210056f72545210074d32545210063e65d05210063d65d05210078d32d0521005b57490521007c532905210063e65505210063d65505210078d3250521007375150521007355150521004f47650521007375450521007355450521007c53250521006b77650521006b47650521007367550521007357550521007366550521007356550521006b66350521006b46350521007375350521007355350521007a77250521007a47250521007375250521007355250521007973250521007a63250521007953250521007a53250521007853250521007c532c8521007a541885210047e75d81210047d75d8121006cd32d8121006b541d81210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d76994210047d74994210047d739942100c7e70994210047f74594210047f735942100c7c70594210047e7519421004be7419421004bd7419421004de7319421004dd7319421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d90210047e75990210047d7599021004bd76990210063e65990210063d65990210063e75990210063d75990210063e65590210063d65590210063e75590210063d75590210047e75190210047d7519021004be7419021004de7319021004dd7319021004f67119021004fa7019021004f970190210047f76d50210047d76d50210063e64d50210063d64d50210056d72d50210047f76550210047d76550210063e64550210063d64550210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c210047e7598c210047d7598c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c210065e7598c210065d7598c210065f5498c210065d5498c210065e6558c210065d6558c210069e6458c210069d6458c210065e7558c210065d7558c210065f5458c210065d5458c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004ee7218c21004fa7018c21004f97018c210047f76d4c210047d76d4c210063e64d4c210063d64d4c210065e63d4c210065d63d4c210057571d4c210047f7654c210047d7654c210063e6454c210063d6454c210065e6354c210065d6354c210047e75988210047d7598821004de7398821004dd73988210047d76d48210053d74d48210063e64d48210063d64d48210065e63d48210065d63d48210047f76548210063e64548210063d64548210065e63548210065d6354821004dd76cc8210065e65cc8210065d65cc8210069e64cc8210069d64cc821004df764c8210065e654c8210065d654
  | 21 => 0xe73992210069d7399221006b671992210063e65592210063d65592210063e75592210063d75592210047e75192210047d75192210047f76d52210047d76d52210063e64d52210063d64d52210056d72d52210047f76552210047d76552210063e64552210063d64552210047e75d8e210047d75d8e21004be74d8e21004bd74d8e210047e7598e210047d7598e210047e7518e210047d7518e21004be7418e21004bd7418e21004fa7018e21004f97018e210047f76d4e210047d76d4e210063e64d4e210063d64d4e210047f7654e210047d7654e210063e6454e210063d6454e210065f6354e210065c6354e210053d74d4a210063e64d4a210063d64d4a210057571d4a210063e6454a210063d6454a21005777154a210065e65cca210065d65cca210069e64cca210069d64cca210065e654ca210065d654ca210069e644ca210069d644ca210063e64d46210063d64d46210055d73d46210063e64546210063d64546210063e65d06210063d65d06210063e65506210063d6550621007375150621007355150621006b66450621007375450621007355450621005b77650621006b77650621007367550621007357550621007366550621007356550621006b66350621006b463506210073753506210073553506210073752506210073552506210079732506210079532506210047f75582210047c7558221004df7358221004dc7358221006b54158221004be7499521004bd7499521004de7399521004dd73995210053d74995210055d73995210063e74995210047d74995210063d74995210043d74995210065e73995210047d73995210065d73995210045d73995210047d72995210066d72995210047d719952100675719952100c7e70995210047f74595210047f73595210047f72595210066f72595210047f715952100677715952100c7c70595210047e75d91210047d75d91210047e75991210047d7599121004de7399121004dd73991210047e75191210047d75191210047f76d51210047d76d51210047f76551210047d76551210063f64551210063c64551210047e75d8d210047d75d8d210047e7598d210047d7598d21004be7498d21004bd7498d210047e7518d210047d7518d210047f76d4d210047d76d4d210047f7654d210047d7654d210065f6354d210065c6354d210053d74d49210057571d49210057771549210065e65cc9210065d65cc921005cd738c9210065e654c9210065d654c9210074f524c9210074d524c921004ec764c9210074f534c9210074d534c921006cf764c921006cc764c9210074e754c9210074d754c9210074e654c9210074d654c921006ce644c921006cc644c9210074f544c9210074d544c921007c7714c921007c4714c9210055d73d45210056d72d45210074d32d45210047f7654521
  | 22 => 0x8031007595358031006ea6258031006e96258031007b141580310067b75580310067875580310067b54580310067954580310067b5358031006da5358031006795358031006d95358031006595358031006da4358031006d943580310067b5258031006795258031006db3258031006d932580310067b5158031006795158031006bb4158031006f24158031006b94158031006f14158031006b14158031006db3158031006f23158031006d93158031006f13158031004de73d9721004dd73d9721004be7499721004bd74997210053d74997210063e74997210047d74997210063d74997210043d74997210047d739972100c7e70997210047f74597210047f735972100c7c7059721004de7319721004dd73197210047e75d93210047d75d9321004de73d9321004dd73d93210047e75993210047d75993210047e75193210047d7519321004de7319321004dd7319321004fa7019321004f970193210047f76d53210047d76d53210047f76553210047d76553210063f64553210063c64553210047e75d8f210047d75d8f210047e7598f210047d7598f21004be7498f21004bd7498f210065e6598f210065d6598f210065e7598f210065d7598f210069e7498f210069d7498f210065f5498f210065d5498f21006ce7298f210065e6558f210065d6558f210065e7558f210065d7558f210065f5458f210065d5458f210047e7518f210047d7518f210047f76d4f210047d76d4f210065e63d4f210065d63d4f210057571d4f210047f7654f210047d7654f210065e6354f210065d6354f210053d74d4b210065e63d4b210065d63d4b210065e6354b210065d6354b210065e65ccb210065d65ccb210065e654cb210065d654cb210074f524cb210074d524cb21006ce634cb210074f534cb210074d534cb21005cf764cb21006cf764cb210074e754cb210074d754cb210074e654cb210074d654cb21006ce644cb21006cc644cb210074f544cb210074d544cb210055d73d47210065e63d47210065d63d47210056d72d47210074d32d47210065e63547210065d63547210056f72547210074d32547210063e65d07210063d65d07210069e63d07210069d63d07210078d32d07210063e65507210063d65507210069e63507210069d63507210078d32507210047f75583210047c7558321004bf7458321004bc7458321006cd3258321004be74d9621004bd74d9621004de7399621004dd73996210055d73996210047d74996210065e73996210047d73996210065d73996210045d739962100c7e70996210047f74596210047f735962100c7c7059621004be7419621004bd74196210047e75d92210047d75d92210047e75992210047d7599221004de7399221004dd73992210063e65992210063d65992210063e75992210063d75992210069
  | 23 => 0x55f7254c310055f7154c310055c7054c31004dd7690c310055d7590c31005cd7290c310055d7550c310069e6450c310047e75988310047d75988310066e65988310066d6598831006ae6498831006ad64988310074d53988310066e75988310066d75988310066f54988310066d54988310066f53988310066d53988310065d53588310066e65588310066d6558831006ae6458831006ad64588310074d53588310066e75588310066d75588310066f54588310066d5458831006ce73588310066f5358831006ce53588310066d5358831006cd53588310064d5358831006ce4358831006cd43588310047f76d48310047d76d48310053d74d48310063e64d48310063d64d48310055d73d48310066e62d48310066d62d48310057571d48310047f76548310047d76548310063e64548310063d64548310066e62548310066d62548310055d75cc8310065e65cc8310065d65cc8310059d74cc8310069e64cc8310069d64cc831006cd62cc831005d571cc8310055d754c8310065e654c8310065d654c8310069e644c8310069d644c831006ce624c8310047e75984310047d7598431004be7498431004bd74984310065d53984310047d76d44310063e64d44310063d64d44310055d73d44310066e62d44310066d62d44310047f76544310063e64544310063d64544310066e62544310066d6254431004bd76d04310063e65d04310063d65d04310071d53d0431006ae62d0431006ad62d0431004f57690431005b57490431007555390431006e56290431004bf76504310063e65504310063d65504310071d5350431006ae6250431006ad6250431007375150431007355150431006b66450431007375450431007355450431007555350431007964350431007954350431006e56250431005b77650431006b77650431007367550431007357550431007366550431007356550431007967350431007957350431006b66350431007375350431007965350431007355350431007955350431007155350431007a66250431006b56250431007a56250431006a562504310073752504310073552504310079732504310079532504310055d75cc431006cd62cc4310079541cc431005b5748c43100755538c431004df764c4310055d754c431006cd624c43100795414c431004f7764c4310067a6598031006796598031006ba6498031006b96498031007595398031006ea6298031006e96298031007b1419803100e7b759803100e7875980310067b54980310067954980310067b53980310067953980310067b5298031006795298031006db3298031006d932980310067b5198031006795198031006bb4198031006b941980310047f75580310047c75580310065d5358031006b541580310067a6558031006796558031006ba6458031006b9645
  | 24 => 0xd74d4a310063e64d4a310063d64d4a310055d73d4a310047f7654a310047d7654a310063e6454a310063d6454a310055d75cca310065e65cca310065d65cca310059d74cca310069e64cca310069d64cca310055d754ca310065e654ca310065d654ca310069e644ca310069d644ca31006ce624ca31006cd624ca310063e64d46310063d64d46310055d73d46310063e64546310063d64546310063e65d06310063d65d06310071d53d06310063e65506310063d65506310071d53506310055d75cc631006b564cc6310047f75582310047c75582310065d5358231004dd73995310047d74995310047d73995310065d73995310045d73995310047d72995310047d719953100675719953100c7e70995310047f74595310047f73595310065f73595310047f72595310047f715953100677715953100c7c70595310047e75d91310047d75d91310047e75991310047d7599131004dd7399131004f571991310047e75191310047d75191310047f76d51310047d76d51310047f76551310047d76551310057571d4d31005777154d310047e75d89310047d75d8931004be74d8931004bd74d89310047e75189310047d75189310047d76d49310053d74d49310047f76549310065e65cc9310065d65cc9310065e654c9310065d654c931006cf624c931005d4714c9310055d73d45310047f76545310047d76545310055f73545310063e65d05310063d65d05310063e65505310063d65505310065d658c5310047e75d81310047d75d81310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131004be74d9431004bd74d9431004ee72d9431004ed72d9431004fa70d9431004f970d94310047d76994310047d74994310065e73994310047d729943100c7e70994310047f74594310047f725943100c7c70594310047e7519431004be7419431004bd7419431004ee7219431004ed7219431004fa7019431004f970194310047e75d90310047d75d9031004ee72d9031004ed72d9031004fa70d9031004f970d90310047e75990310047d7599031004bd76990310063e65990310063d65990310063e75990310063d75990310069e7399031006b671990310063e65590310063d65590310063e75590310063d75590310047e75190310047d7519031004be7419031004ee7219031004ed7219031004fa7019031004f970190310047f76d50310047d76d50310063e64d50310063d64d50310055d73d50310047f76550310047d76550310063e64550310063d64550310047e7598c310047d7598c310047d76d4c310063e64d4c310063d64d4c31004dd7694c310055d7594c310047f7654c310063e6454c310063d6454c310065e6554c310055f7654c310065f7654c310055f7454c310071e6454c310071d6454c31
  | 25 => 0x90410069d73990410047d76d50410063e64d50410047f76550410063e64550410047e7598c410047d7598c410047f76d4c410047d76d4c410063e64d4c410047f7654c410047d7654c410063e6454c410047e75988410047d7598841004de7398841004dd73988410047f76d48410047d76d48410053d74d48410063e64d48410047f76548410047d76548410063e64548410065e65cc8410065d65cc8410069e64cc8410065e654c8410065d654c8410069e644c841006ce624c841006cd624c8410047e75984410047d75984410047d76d44410063e64d44410055d73d44410047f76544410063e64544410063e65d04410063d65d0441004bf76504410063e65504410063d6550441007355150441004f77650441006b664504410073554504410047f75580410047c75580410047d74997310047d729973100c7e70997310047f74597310047f725973100c7c70597310047e75d93310047d75d9331004ee72d9331004ed72d93310047e75993310047d75993310047e75193310047d75193310047f76d53310047d76d53310047f76553310047d76553310047e7598b310047d7598b310047f76d4b310047d76d4b310053d74d4b310057571d4b310047f7654b310047d7654b310065e65ccb310065d65ccb31006cd62ccb310065e654cb310065d654cb310055d73d47310055f73547310063e65d07310063d65d07310063e65507310063d6550731007375150731007355150731007375450731007355450731006b77650731006b47650731007367550731007357550731007366550731007356550731007977350731007947350731007375350731007355350731006b562507310073752507310073552507310079732507310079532507310047f75583310047c7558331006b54158331004be74d9631004bd74d96310047d74996310065d73996310047d729963100c7e70996310047f74596310047f725963100c7c7059631004be7419631004bd74196310047e75d92310047d75d92310047e75992310047d75992310063e65992310063d65992310063e75992310063d75992310069d73992310063e65592310063d65592310063e75592310063d75592310047e75192310047d75192310047f76d52310047d76d52310063e64d52310063d64d52310055d73d52310047f76552310047d76552310063e64552310063d64552310063e64d4e310063d64d4e310057571d4e310065e6594e310063e6454e310063d6454e31005777154e310065f7654e310065c7654e310055f7454e310071e6454e310071d6454e310055f7254e310055f7154e31007577154e31007547154e310055c7054e310055d7590e310069e6490e31005cd7290e310055d7550e310047e7598a310047d7598a310065d5358a310047f76d4a310047d76d4a310053
  | 26 => 0x7377154d41005377154d41007347154d410053c7054d410053e7514d410053e75d89410053d75d89410053e75989410053d75989410063d65989410059e73989410059d7398941005b57198941005b771589410053e75189410053d75189410063d65189410059e73189410059d7318941006ad6218941005ba7018941005b97018941004be76d4941004bd76d49410053f76d49410063e76d49410053d76d49410063d76d49410043d76d49410053d73d49410053d71d49410053e70d49410053d75949410059e73949410059d7394941005b67194941005b571949410053f76549410053d76549410053f73549410072f72549410072f62549410072c62549410053f71549410053c70549410053e75149410059e73149410059d7314941005b67114941005b57114941004be76cc941004bd76cc9410053e75cc9410053d75cc9410071f53cc9410071d53cc9410069e76cc9410069d76cc9410071e75cc9410071d75cc9410071e65cc9410071d65cc9410071f52cc9410071d52cc9410079771cc9410079471cc9410053e758c9410053d758c9410059d738c941005b6718c941005b5718c9410053e754c9410053d754c9410071f534c9410071d534c941005b7714c941005b4714c9410071e754c9410071d754c9410071e654c9410071d654c9410078f724c9410078f624c9410078c624c9410071f524c9410071d524c94100797714c94100794714c9410053e750c9410053d750c9410059e730c941005b6710c941005b5710c9410053e75d85410053d75d85410063e65d85410063d65d85410059e73d85410059d73d85410073675d85410073575d85410073665d85410073565d8541005b673d85410079673d85410059673d85410079573d85410073753d85410073553d8541005b572d85410073752d85410073552d85410079732d85410079532d8541005b570d85410059e73d45410059d73d45410071e73d45410053d73d45410071d73d45410051d73d45410053d72d45410071f32d45410071d32d45410073761d45410053e70d4541004be76945410053d75945410073751945410053f76545410053d76545410053f73545410053f72545410071f32545410071d32545410073771545410073761545410053c7054541004be76145410053e75145410053e75d81410053d75d81410063d65d81410053f75581410053c75581410063d65581410059f73581410059c7358141005af7258141005ac72581410053e75181410053d75181410059e73181410059d7318141005ae7218141005ad7218141004be74d94410047d76994410047d73994410047d729944100c7e70994410047f73594410047f725944100c7c70594410047e7519441004be74194410047e75990410047d75990410063e75990410063d75990410069e739
  | 27 => 0xf715954100677715954100c7c70595410057571d5141004be76d51410063f65d5141005b671d51410063e76d51410063d76d51410053d73d51410053d72d51410073671d51410073571d51410053e70d51410053d75951410063e6595141005777155141004bc76551410063f76551410063c76551410053f73551410053f72551410073771551410073471551410053c70551410053e75151410047e75d8d410047d75d8d410047e7518d410047d7518d410047d76d4d410053d74d4d410057571d4d410047f7654d410053f7454d410065f6354d410065c6354d41005777154d410053e75d0d410053d75d0d41005b671d0d410053e7590d410053d7590d41005ae7290d41005ad7290d410053e7550d410053d7550d41005b47150d410053e7510d410053d7510d410047e75d89410047d75d89410047e75189410047d75189410063d5418941004de7318941004dd7318941004fa7018941004f970189410047d76d49410053d74d49410047f76549410053f74549410066f62549410066c62549410053e75d09410053d75d09410053e75909410053d75909410063d65909410059e73909410059d7390941005b671909410053e75509410053d7550941006ac62509410053e75109410053d75109410063d65109410059e73109410059d7310941005b67110941005ba7010941005b970109410065e65cc9410065d65cc9410071f54cc9410071d54cc9410065e654c9410065d654c9410071f544c9410071d544c941006cf624c941006cc624c9410078f424c9410078c424c9410053d74d45410055d73d45410047f76545410047d76545410053f74545410073754d05410073554d0541005d673d05410053e75905410053d75905410047e75d81410047d75d81410063d54d81410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed72181410063f65995410059e73995410059d7399541005ae7299541005ad7299541005b571995410071e73995410053d73995410071d73995410051d73995410072e72995410053d72995410072d72995410052d72995410053d71995410073571995410053571995410053e7099541005b771595410063f76595410053f73595410053f72595410053f71595410073771595410053771595410053c70595410053e75d8d410053d75d8d410053e7598d410053d7598d41005ae7298d41005ad7298d41005b57198d41005b77158d410053e7518d410053d7518d41005b671d4d41005b571d4d410053f76d4d410053d76d4d410053d72d4d410073671d4d410053d71d4d410073571d4d410053571d4d410053e70d4d410053d7594d41005b77154d41005b47154d410053f7654d410053d7654d410071f7354d410071f6354d410071c6354d410053f7254d410053f7154d41
  | 28 => 0x8b410053e7518b410053d7518b410063d6518b410059e7318b410059d7318b410069d6318b41006ad6218b41005b57118b41005ba7018b41005b97018b41004be76d4b41004bd76d4b410053f76d4b410063e76d4b410053d76d4b410063d76d4b410043d76d4b410053d73d4b410071e63d4b410071d63d4b410053d71d4b410053e70d4b410059e7394b410059d7394b410053f7654b410053d7654b410053f7354b410071e6354b410071d6354b410072f7254b410053f7154b410053c7054b410059e7314b410059d7314b41004be76ccb41004bd76ccb410053e75ccb410053d75ccb410071f53ccb410071d53ccb410059f76ccb410069e76ccb410059d76ccb410069d76ccb410049d76ccb410071e75ccb410071d75ccb410071e65ccb410071d65ccb410071f52ccb410071d52ccb410053e758cb410053d758cb410053e754cb410053d754cb410071f534cb410071d534cb410059f764cb410059d764cb410071e754cb410071d754cb410071e654cb410071d654cb410078f724cb410078f624cb410078c624cb410071f524cb410071d524cb410053e750cb410053d750cb410059e73d47410059d73d47410053d76d47410071e73d47410053d73d47410071d73d47410051d73d47410071e63d47410071d63d47410053d72d47410071f32d47410071d32d47410053e70d47410053f76547410053f73547410071e63547410071d63547410053f72547410071f32547410071d32547410073771547410053c70547410053e75d83410053d75d83410063d65d83410059e73d83410059d73d83410069d63d83410053f75583410053c75583410063d65583410069d63583410053e75183410053d75183410059e73183410059d7318341005ae7218341005ad72183410047d73996410047d729964100c7e70996410047f73596410047f725964100c7c70596410057571d52410057771552410047e7598e410047d7598e410047f76d4e410047d76d4e410057571d4e410047f7654e410047d7654e41005777154e410047e7598a410047d7598a41004de7398a41004dd7398a410047f76d4a410047d76d4a410053d74d4a410047f7654a410047d7654a410065e65cca410065d65cca410065e654ca410065d654ca41006ce624ca41006cd624ca410055d73d46410063e65d06410063d65d06410073551d06410073554d0641005d673d06410047f75582410047c7558241004de7399541004dd7399541004ee7299541004ed72995410055d73995410056d72995410047d74995410063d74995410065e73995410047d73995410065d73995410045d73995410066e72995410047d72995410066d72995410046d72995410047d719954100675719954100c7e70995410047f74595410063f74595410047f73595410047f72595410047
  | 29 => 0x5b671153410047e7598f410047d7598f41004ee7298f41004ed7298f410065e6598f410065d6598f410071f5498f410071d5498f41005cd7298f410065e7598f410065d7598f410065f5498f410065d5498f41006ce7298f41004dd7298f41006cd7298f41004cd7298f410065e6558f410065d6558f410071f5458f410071d5458f410065e7558f410065d7558f410065f5458f410065d5458f41004df7258f410047f76d4f410047d76d4f410053d74d4f410065e63d4f410065d63d4f410047f7654f410047d7654f410053f7454f410065e6354f410065d6354f410053e75d0f410053d75d0f410053e7590f410053d7590f410069d6390f41005ae7290f41005ad7290f410053e7550f410053d7550f410069e6350f410053e7510f410053d7510f410047e7598b410047d7598b410063d5498b41004de7398b41004dd7398b410047f76d4b410047d76d4b410053d74d4b410065e63d4b410065d63d4b410047f7654b410047d7654b410053f7454b410065e6354b410065d6354b410053e75d0b410053d75d0b410053e7590b410053d7590b410063d6590b410059e7390b410059d7390b410069d6390b410053e7550b410053d7550b410053e7510b410053d7510b410063d6510b410059e7310b410059d7310b410069d6310b41006ad6210b41005ba7010b41005b97010b41004df76ccb41004dd76ccb410065e65ccb410065d65ccb410071f54ccb410071d54ccb41004df764cb41004dd764cb410065e654cb410065d654cb410071f544cb410071d544cb410078f424cb410078c424cb410053d74d47410055d73d47410065e63d47410065d63d47410053f74547410065e63547410065d63547410047f75583410047c75583410063d54583410059e73d97410059d73d9741005b571d97410063f65997410053d73997410053d72997410053e70997410063f76597410053f73597410053f72597410053c70597410059e73197410059d7319741005b571197410053e75d8f410053d75d8f41005b571d8f410053e7598f410053d7598f41005ae7298f41005ad7298f410071e7598f410071d7598f410071e6598f410071d6598f410078e7298f410059d7298f410078d7298f410058d7298f410069f7658f410071e7558f410071d7558f410071e6558f410071d6558f410059f7258f410053e7518f410053d7518f41005b57118f410053f76d4f410053d76d4f410071e63d4f410071d63d4f410053d72d4f410053d71d4f410053e70d4f410053f7654f410053d7654f410071f7354f410071e6354f410071d6354f410053f7254f410053f7154f410053c7054f410053e75d8b410053d75d8b410059e73d8b410059d73d8b41005b571d8b410053e7598b410053d7598b410063d6598b410059e7398b410059d7398b410069d639
  | 30 => 0xd74d8d510047d72d8d5100c7e70d8d51005757198d51005777158d510065d6318d510047e76d0d510047d76d0d510057671d0d510057571d0d510047e7690d510047d7690d510065f6390d510056e7290d510056d7290d510047e7650d510065f6350d510047e7610d510047d7610d510053e74d89510053d74d89510063e74d89510047d74d89510063d74d89510043d74d89510047d73d895100c7e70d89510055e73989510055d73989510057571989510057771589510055e73189510055d73189510047e76d09510047d76d09510047e76909510047d76909510055e73909510055d73909510047e76509510047e76109510047d76109510055e73109510055d73109510057671109510057571109510057a70109510057970109510047e76cc9510047d76cc9510053e74cc9510053d74cc9510065f63cc9510065e76cc9510065d76cc9510071e74cc9510071d74cc9510065f64cc9510065f62cc9510047e768c9510047d768c9510055d738c9510047e764c9510065f634c95100577714c95100574714c9510065e764c9510065d764c9510065f644c9510074f724c9510065f624c9510074f424c9510074c424c95100757714c95100754714c9510047e760c9510047d760c9510055e730c9510055e73d85510055d73d85510075673d85510075573d85510075732d85510075532d85510057570d85510055f73581510055c73581510053e74181510053d74181510055e73181510055d73181510056e72181510056d721815100e3e74181510047d741815100e3d74181510043d741815100e5e73181510047d731815100e5d73181510045d731815100e6e72181510047d721815100e6d72181510046d72181510065f32181510065d32181510065e73994510065d73994510063e75590510063e64d50510063d64d50510047f76550510063e64550510063e64d4c510063d64d4c510065d63d4c510047f7654c510063e6454c510063d6454c51004de7398851004dd73988510053d74d48510063e64d48510063d64d48510066d62d48510047f76548510063e64548510063d64548510065e65cc8510069e64cc8510069d64cc8510065e654c8510069e644c8510069d644c851006ce624c851006cd624c8510063e64d44510063d64d44510055d73d44510047f76544510063e64544510063d6454451004f77654451006766554451004de73d9741004dd73d97410063e74997410047d73997410047d729974100c7e70997410063c74597410047f73597410047f725974100c7c7059741004de7319741004dd73197410063f65d53410063d65d53410053d76d53410063d76d53410053d73d53410053d72d53410053e70d53410063e65953410063e65553410053f76553410063f76553410053f73553410053f72553410053c7055341
  | 31 => 0x8f510047e76d0f510047d76d0f510065d63d0f510057671d0f510057571d0f510047e7690f510047d7690f510065d6390f510056e7290f510056d7290f510047d7650f510065d6350f510047e7610f510047d7610f510065d6310f510053e74d8b510053d74d8b510055e73d8b510055d73d8b510065e63d8b510065d63d8b510057571d8b510055e7398b510055d7398b510065d6398b510065e6358b510065d6358b510047f7458b510047f7358b510065e7358b510065d7358b5100c7c7058b510055e7318b510055d7318b510065d6318b51005757118b510047e76d0b510047d76d0b510065d63d0b510066d62d0b510047e7690b510047d7690b510063d6490b510055e7390b510055d7390b510065d6390b510047d7650b510065d6350b510047e7610b510047d7610b510063d6410b510055e7310b510055d7310b510065d6310b510066d6210b51005767110b51005757110b510057a7010b51005797010b510047e76ccb510047d76ccb510053e74ccb510053d74ccb510065d63ccb510055f76ccb510065e76ccb510055d76ccb510065d76ccb510045d76ccb510071e74ccb510071d74ccb510065d64ccb510065d62ccb510047e768cb510047d768cb510065d638cb510047d764cb510065d634cb510055f764cb510065e764cb510055d764cb510065d764cb510045d764cb510065d644cb510074f724cb510065d624cb510074f424cb510074c424cb510047e760cb510047d760cb510065d630cb510055e73d83510055d73d83510065d63d83510065e63983510065d63983510047d74983510047d73983510047d72983510065f32983510065d32983510065d63583510053e74183510053d74183510055e73183510055d73183510065e63183510065d63183510056e72183510056d72183510063d75592510063e64d52510063e64552510063d64552510063e64d4e510063d64d4e510063e6454e510063d6454e510065d6354e51004de7398a51004dd7398a510053d74d4a510063e64d4a510063d64d4a510063e6454a510063d6454a510066d6254a510069e64cca510069d64cca510069e644ca510069d644ca51006ce624ca51006cd624ca510063e64d46510063d64d46510055d73d46510063f64951510063f64551510047e76151510065f6354d510065c6354d510047e7614d51004be74d8951004bd74d8951004de7318951004dd73189510053e74d49510053d74d49510055e73949510055d73949510066f62549510047e76149510055e73149510055d73149510053e74945510053d7494551004be7418151004bd7418151004de7318151004dd7318151004ee7218151004ed72181510047d73d91510047d72d915100c7e70d91510063f64991510055e73991510055d73991510057571991510057771591510047
  | 32 => 0x55e75d85320055d75d85320055e75985320055d75985320065d65985320059e74985320059d74985320055e75185320055d75185320065d65185320059e74185320059d7418532006d56118532005da7018532005d970185320055e75d81320055d75d81320065d65d81320055f75581320055c75581320065d65581320059f74581320059c7458132005d77158132005d471581320055e75181320055d75181320059e74181320059d7418132005d67118132005d57118132004de73d94320047d76994320047d74994320047d719943200c7e70994320047f74594320047f715943200c7c70594320047e7519432004de73194320047e75d90320047d75d9032004de73d9032004ee72d90320047e75990320047d75990320047e75190320047d7519032004de7319032004f67119032004f57119032004fa7019032004f970190320047f76d50320047d76d50320047f76550320047d76550320047e7598c320047d7598c32004be7498c32004bd7498c320065e7598c320065d7598c320069e7498c320069d7498c320065f5498c320065d5498c320047d76d4c320065e63d4c320047f7654c320065e6354c320047e75988320047d75988320047d76d48320053d74d48320065e63d48320047f76548320065e63548320065e65cc8320065d65cc832004df764c8320065e654c8320065d654c8320074d524c832004ef764c832006ce634c8320074d534c8320047e75984320047d7598432004be7498432004bd74984320047f75580320047c75580320063e64d53510063d64d53510057671153510065f5498f510065d5498f51004dd7298f510065e7558f510065f5458f510065e5458f510065d5458f510065c5458f51004df7258f510065d63d4f510065d6394f510065e6354f510065d6314f51004de7398b51004dd7398b510053e74d4b510053d74d4b510065e63d4b510065d63d4b510066d62d4b510055e7394b510055d7394b510065d6394b510065e6354b510065d6354b510055e7314b510055d7314b510065d6314b51004df76ccb51004dd76ccb51004df764cb51004dd764cb510055e73d93510055d73d93510056e72d93510056d72d93510057571d93510063f64993510047f73593510047f725935100c7c70593510055e73193510055d73193510057571193510057571d8f510065f6498f510065d6498f510055d7298f510047f7458f510047f7258f5100c7c7058f510065f7658f510065f6458f510065e6458f510065d6458f510065c6458f510055f7258f510065f7458f510065e7458f510065d7458f510065c7458f510065f7258f510045f7258f510065e7258f510065d7258f510065c7258f510065f7158f510065d7158f510065f7058f510065e7058f510065d7058f510065c7058f510065d6318f5100575711
  | 33 => 0xe7418532004bd74185320065d5318532004fa7018532004f970185320047e75d81320047d75d81320065d53d81320047e75181320047d7518132004be7418132004bd7418132004f67118132004f571181320059e74995320059d7499532005cd7299532005d67199532005d571995320071e74995320055d74995320071d74995320051d74995320055d72995320074d72995320054d72995320075671995320055d71995320075571995320055571995320055e7099532005cf72595320065f76595320055f74595320055f72595320074f72595320054f72595320055f71595320055c70595320055e75d91320055d75d91320055e75991320055d7599132005cd7299132005d67199132005d57199132005cf72591320055e75191320055d7519132005ce72d5132005cd72d51320055f76d51320055d76d51320074e72d51320055d72d51320074d72d51320054d72d51320055d71d51320055e70d51320055d75951320071f5495132005cf7255132005cc72551320055f76551320055d76551320071f74551320071f64551320071c64551320055f72551320074f72551320054f72551320074c72551320055f71551320055c70551320055e75151320055e75d89320055d75d89320065e65d89320065d65d89320059e74d89320059d74d89320074e75d89320074d75d89320074e65d89320074d65d8932005ce74d89320078e74d89320058e74d89320078d74d89320074f54d89320074d54d8932005cd71d8932005cd70d89320059e74d49320059d74d49320071e74d49320055d74d49320071d74d49320051d74d49320074f62d49320055d71d49320055e70d4932004de76949320055d75949320074f52949320055f76549320055d76549320055f74549320074f72549320074f62549320055f71549320055c7054932004de76149320055e75149320055e75d09320055d75d09320074f52d09320074d52d0932005ce76d0932005cc76d09320074e75d09320074d75d09320074e65d09320074d65d09320078f64d09320078c64d09320074f54d09320074d54d0932005cd71d0932005cd70d0932004de76909320055e75909320055d75909320071d5490932005ce72909320055e75509320055d7550932004de76109320055e75109320055d75109320071d54109320074f52109320074d52109320078d4210932005d67110932005d57110932005da7010932005d97010932005ce7610932006ce76109320074e75109320074d75109320074e65109320074d6510932005ce74109320078e74109320078e64109320078d64109320074f54109320078e54109320074d54109320078d54109320070d5410932007c67110932005cd7110932007c57110932005c57110932007ca7010932005cd7010932007c97010932005c97010932
  | 34 => 0x87320059d74987320069d64987320055e75187320055d75187320065d65187320059e74187320059d74187320069d6418732006d56118732005da7018732005d970187320055e75d83320055d75d83320065d65d83320059e74d83320059d74d83320069d64d83320055f75583320055c75583320065d65583320069d64583320055e75183320055d75183320059e74183320059d7418332005d67118332005d571183320047d74996320047d719963200c7e70996320047f74596320047f715963200c7c70596320047e75d92320047d75d92320047e75992320047d75992320047e75192320047d7519232004f67119232004f57119232004fa7019232004f970192320047f76d52320047d76d52320056d72d52320047f76552320047d76552320056f72552320056d72d4e320056f7254e320053d74d4a320072d5410a32005e57110a32005e97010a320065e65cca320065d65cca320074d52cca32005ae74cca320074d53cca320047e75986320047d7598632004be7498632004bd74986320047f75582320047c7558232004be7499532004bd7499532004f67199532004f571995320053d74995320057571995320063e74995320047d74995320063d74995320043d74995320047d73995320065d73995320047d72995320066d72995320067671995320047d719953200675719953200475719953200c7e70995320047f74595320047f73595320065f73595320047f72595320066f72595320047f715953200c7c70595320047e75d91320047d75d91320047e75991320047d7599132004f67199132004f571991320047e75191320047d75191320047f76d51320047d76d51320055d73d51320056d72d51320047f76551320047d76551320063f64551320063c64551320055f73551320056f72551320056d72d4d32004de76d4d32005ce72d4d320065e76d4d320065d76d4d320055d74d4d320074e72d4d320074d72d4d320055d71d4d320055e70d4d320055d7594d320056f7254d32004dc7654d320065f7654d320065c7654d320055f7454d320074f7254d320074c7254d320055f7154d320055c7054d320055e7514d32004de76d0d320055e75d0d320055d75d0d32005d671d0d32005d571d0d320055e7590d320055d7590d32005ce7290d32004dc7650d320055e7550d320055d7550d32005cc7250d320055e7510d320055d7510d320053d74d49320055d73d49320047f76549320047d76549320055f7354932004ee76d09320074f53d09320074d53d09320072d5410932005ce73109320074f53109320074d53109320078f43109320078d4310932005e57110932005e97010932005ae74cc9320074f53cc9320074d53cc9320055e758c9320055d758c9320047e75d85320047d75d85320047e75185320047d7518532004b
  | 35 => 0x4f67199332004f571993320063e65993320063d6599332005b571993320063e75993320063d75993320069e7399332006b67199332004bd7199332006b57199332004b571993320063e65593320063d65593320063e75593320063d75593320069c7359332004bf71593320047e75193320047d75193320047f76d53320047d76d53320063e64d53320063d64d53320055d73d53320047f76553320047d76553320063e64553320063d64553320055f73553320063e64d4f320063d64d4f320065d65d4f320055d76d4f320065d76d4f320055d74d4f320071e64d4f320071d64d4f320055d71d4f320055e70d4f320063e6454f320063d6454f320065e6554f320055f7654f320065f7654f320055f7454f320071e6454f320071d6454f320055f7154f320055c7054f32005ce7214f320055e75d0f320055d75d0f320069d64d0f32005d671d0f32005d571d0f320055e7590f320055d7590f320055e7550f320055d7550f320069e6450f320055e7510f320055d7510f320053d74d4b320063e64d4b320063d64d4b320055d73d4b320063e6454b320063d6454b320055f7354b320047e75987320047d7598732004be7498732004bd74987320065d53987320047f75583320047c75583320065d53583320059e74d97320059d74d9732005cd72d97320055d74997320055d71997320055e70997320065f76597320055f74597320055f71597320055c70597320059e74197320059d7419732005cd72197320055e75d93320055d75d9332005cd72d93320055e75993320055d7599332005d67199332005d571993320071e75993320071d75993320071e65993320071d65993320079671993320059d71993320079571993320059571993320069f76593320071e75593320071d75593320071e65593320071d65593320059f71593320055e75193320055d7519332005cd72193320055f76d53320055d76d53320071e64d53320071d64d53320055d72d53320055d71d53320055e70d53320071f54953320055f76553320055d76553320071f74553320071e64553320071d64553320055f72553320055f71553320055c70553320059e74d4b320059d74d4b320055d76d4b320071e74d4b320055d74d4b320071d74d4b320051d74d4b320071e64d4b320071d64d4b320055d71d4b320055e70d4b320055f7654b320055f7454b320071e6454b320071d6454b320074f7254b320055f7154b320055c7054b320055e75d0b320055d75d0b320055e7590b320055d7590b320071d5490b320055e7550b320055d7550b320055e7510b320055d7510b320071d5410b32005d67110b32005d57110b32005da7010b32005d97010b320055e75d87320055d75d87320059e74d87320059d74d87320055e75987320055d75987320065d65987320059e749
  | 36 => 0x970d94420047d76994420063e74994420047d73994420047d719944200c7e70994420047f73594420047f715944200c7c70594420047e7519442004de7319442004dd7319442004f67119442004f57119442004fa7019442004f970194420047e75990420047d75990420047d76d5042004bd76950420053d75950420063e65950420047f76550420063e65550420053f76550420063f76550420053f73550420053f72550420053f71550420053c70550420047e7598c420047d7598c420065e6598c420065d6598c420071d5498c420065e7598c420065d7598c420065f5498c420065d5498c42006ce7298c420065e6558c420065d6558c420071d5458c420065e7558c420065d7558c420065f5458c420065d5458c420047f76d4c420047d76d4c420053d74d4c420065e63d4c420065d63d4c420047f7654c420047d7654c420065e6354c420065d6354c420053d75d0c42005b571d0c420053d7550c420069e6350c420047e75988420047d75988420063d54988420047d76d48420053d74d48420065e63d48420065d63d48420047f76548420065e63548420065d63548420053d75d08420072d5490842005cd7390842004bf76508420053d7550842004ef76508420047e75984420047d7598442006766598442006756598442007355498442006d66398442006d563984420067675984420067575984420067754984420067554984420067753984420067553984420067752984420067552984420063d5458442006766558442006756558442007355458442006d66358442006d56358442006767558442006757558442006b67458442006775458442006b65458442006755458442006b55458442006355458442006775358442006755358442006b74358442006b54358442006775258442006755258442006b74258442006b542584420067a6598042006796598042007395498042006da6398042006d96398042006f26198042006f1619804200e7b759804200e7875980420067b54980420067954980420067b53980420067953980420067b52980420067952980420047f75580420047c75580420063d54580420067a6558042006796558042007395458042006da6358042006d96358042006f26158042006f161580420067b75580420067875580420067b5458042006ba5458042006795458042006b954580420063954580420067b5358042006795358042006bb4358042006b943580420067b5258042006795258042006bb4258042006ea4258042006b94258042006e94258042004be74d9732004bd74d97320047d74997320065e73997320047d719973200c7e70997320047f74597320065c73597320047f715973200c7c7059732004be7419732004bd74197320047e75d93320047d75d93320047e75993320047d7599332
  | 37 => 0x815200576711815200575711815200e3e74181520047d741815200e3d74181520043d741815200e5e73181520047d731815200e5d73181520045d731815200e7671181520047d711815200e7571181520047571181520063e74994520063d74994520063e64d50520063d64d50520047f76550520065f5498c520065d5498c520065e7558c520065f5458c520065d5458c520065e63d4c520065d63d4c520047f7654c520065e6354c520053d74d48520065e63d48520065d63d48520047f76548520065e63548520065d6354852004ef76548520066e6554852004be7498452004bd74984520047d73997420047d719974200c7e70997420047f73597420047f715974200c7c70597420047e7598f420047d7598f420047f76d4f420047d76d4f420047f7654f420047d7654f420053d74d4b420053f7454b420047e75987420047d75987420047f75583420047c7558342004de73d9642004dd73d96420063d74996420047d73996420047d719964200c7e70996420047f73596420047f715964200c7c7059642004de7319642004dd73196420056d72d52420063e65952420056f72552420063f76552420063c76552420053f73552420053f72552420072f72552420072c72552420053f71552420053c70552420047e7598e420047d7598e420065e6598e420065d6598e420071d5498e420065e7598e420065d7598e420065f5498e420065d5498e420065e6558e420065d6558e420071d5458e420065e7558e420065d7558e420065f5458e420065d5458e420047f76d4e420047d76d4e420053d74d4e420065e63d4e420065d63d4e420047f7654e420047d7654e420065e6354e420065d6354e420053d75d0e420069e63d0e42005b571d0e420053d7550e420053d74d4a420065e63d4a420065d63d4a420065e6354a420065d6354a420053d75d0a420072d52d0a420072d54d0a42006cd63d0a420047e75986420047d75986420063d54586420047f75582420047c75582420063d5458242004bd74995420047d74995420063d74995420043d74995420047d73995420047d72995420066d72995420047d719954200c7e70995420047f74595420063f74595420047f73595420047f72595420066f72595420047f715954200c7c70595420056d72d51420056f72551420047e75d8d420047d75d8d420047e7518d420047d7518d420047d76d4d420047f7654d420053d74d49420047f76549420047d76549420053f74549420063d65909420047e75d85420047d75d8542004de73d8542004dd73d85420047e75185420047d75185420047e75d81420047d75d81420047e75181420047d7518142004de7318142004dd7318142004f67118142004f57118142004de73d9442004dd73d9442004f671d9442004f571d9442004fa70d9442004f
  | 38 => 0x47f715935200c7c70593520063f76593520053f71593520063f73593520063e73593520063d73593520063c73593520063f72593520063d72593520063f71593520043f71593520063e71593520063d71593520063c71593520063f70593520063e70593520063d70593520063c70593520063d64193520056d72193520053e74d8f520053d74d8f520063e64d8f520063d64d8f520056d72d8f520057671d8f520057571d8f520063d6498f520063e6458f520063d6458f520047f7458f520047f7158f5200c7c7058f520053e7418f520053d7418f520063d6418f520056d7218f520047e76d0f520047d76d0f520063d64d0f520057671d0f520057571d0f520047e7690f520047d7690f520063d6490f520056e7290f520056d7290f520047d7650f520063d6450f520047e7610f520047d7610f520063d6410f520053e74d87520053d74d87520063e64d87520063d64d87520055e73d87520055d73d87520053e74987520053d74987520063d64987520063e64587520063d64587520047f74587520063e74587520063d74587520047f735875200c7c70587520053e74187520053d74187520063d64187520053e74d83520053d74d83520063d64d83520063e64983520063d64983520047d74983520047d73983520047d71983520063d64583520053e74183520053d74183520063e64183520063d64183520055e73183520055d73183520057671183520057571183520063d64552520065f5498e520065d5498e520065d7558e520065f5458e520065d5458e520065e63d4e520065e6354e520065d6354e520053d74d4a520065e63d4a520065d63d4a52004be7498652004bd74986520063f64951520063f64551520063c64551520047e76151520065f6354d520047e7614d520055e73949520055d7394952004de73d8552004dd73d8552004be7418552004bd7418552004be7418152004bd7418152004de7318152004dd7318152004f67118152004f571181520047d73d91520047d71d915200c7e70d91520063f64991520056d72991520056f72591520063d64191520047d74d8d520047d71d8d5200c7e70d8d520053e7498d520053d7498d520056d7298d520056f7258d520047e76d0d520047d76d0d520063f64d0d520057671d0d520057571d0d520047e7690d520047d7690d520056e7290d520056d7290d520047e7650d520063f6450d520047e7610d520047d7610d520053e74d89520053d74d89520072e74d89520072d74d89520056d70d89520055e73d85520055d73d85520047d74d85520065e73d85520047d73d85520065d73d85520045d73d855200c7e70d85520053e74985520053d74985520053e74185520053d74185520053f74581520053c74581520053e74181520053d74181520055e73181520055d731
  | 39 => 0xf76550530047f7654c53004df7654c530065e6554c53004be7498453004bd7498453004f671d9743004f571d97430047d72997430047d719974300c7e70997430047f72597430047f715974300c7c7059743004f67119743004f571197430053d74d4f430053f7454f430047e7598b430047d7598b430047e75987430047d7598743006766598743006756598743006767598743006757598743006775498743006755498743006775398743006755398743006766558743006756558743006767558743006757558743006b674587430067754587430067554587430067753587430067553587430047f75583430047c7558343004ee72d9643004ed72d96430047d72996430047d719964300c7e70996430047f72596430047f715964300c7c7059643004ee7219643004ed72196430055d73d52430055f73552430071d53d0e43005b571d0e430071d54d0e43005d671d0e430047e7598a430047d7598a430066e6598a430066d6598a430066e7598a430066d7598a430066f5498a430066d5498a430066f5398a430066d5398a43006af4398a430066e6558a430066d6558a430066e7558a430066d7558a430066f5458a430066d5458a43006ce7358a430066f5358a430066d5358a43006cf4358a430047e75986430047d75986430047f75582430047c75582430047d74995430063d74995430047d73995430065d73995430047d72995430047d719954300c7e70995430047f74595430063f74595430047f73595430065f73595430047f72595430047f715954300c7c70595430055d73d51430055f73551430053d74d4d430047f7654d430047d7654d430053f7454d43005d671d0d43005ae7290d430047e75d89430047d75d89430047e75189430047d75189430047e75d85430047d75d85430047e75185430047d75185430047e75d81430047d75d81430047e75181430047d7518143004ee7218143004ed7218143004f67118143004f571181430047d76994430047d72994430047d719944300c7e70994430047f72594430047f715944300c7c70594430047e75194430047e75990430047d75990430047d76d50430047f76550430047e7598c430047d7598c430047d76d4c430047f7654c43005b571d0c43005cd7290c43004bf7650c430071d5350c43004df7650c430071d5450c430047e75988430047d75988430047e75984430047d75984430047f75580430047c7558043004bd71993520063e7559352004bf71593520063e64d53520063d64d53520063d64953520063e64553520063d64153520056e72153520063e64d4f520063d64d4f520065d63d4f520063d6494f520063e6454f520063d6454f520063d6414f520056e7214f52004be7498752004bd74987520056d72d93520063f64993520053d71993520047f7359352
  | 40 => 0x83540056e72183540056d72183540057671183540057571183540053d76d52540063d76d52540053d71d5254004de7398a54004dd7398a540063f5458654004de7318954004dd7318954004de73d8554004dd73d8554004de7318154004dd7318154004ee7218154004ed7218154004f67118154004f571181540053e72d91540053d71d91540053d70d91540047d72d8d540047d71d8d5400c7e70d8d540056e7298d540056d7298d540047d73d89540047d71d895400c7e70d89540055e73989540055d73989540055e73189540055d73189540063f64d85540055e73d85540055d73d85540063f74d85540065e73d85540047d73d85540065d73d85540045d73d85540047d72d855400c7e70d85540055e73181540055d73181540056e72181540056d721815400576711815400575711815400e5e73181540047d731815400e5d73181540045d731815400e6e72181540047d721815400e6d72181540046d721815400e7671181540047d711815400e7571181540047571181540063e65950540047f7655054004bf76550540063e6555054004de7398854004dd73988540063e64d53530063d64d53530055e7315353004be7498753004bd74987530055d73d93530063f64993530047f72593530047f715935300c7c70593530055d73193530057671193530057571193530053e74d8b530053d74d8b530057671d8b530057571d8b530047f7458b530065d7358b530047f7158b5300c7c7058b530053e74987530053d74987530047f74587530047f725875300c7c70587530053e74187530053d74187530047d74983530047d72983530047d71983530053e74183530053d74183530056e72183530056d72183530057671183530057571183530063d6455253004be7498653004bd74986530063f64951530063f64551530047e7615153004be74d8953004bd74d8953004be7418553004bd7418553004be7418153004bd7418153004ee7218153004ed7218153004f67118153004f571181530047d72d91530047d71d915300c7e70d91530063f64991530055d73991530057671991530057571991530055f73591530055d72d8d530055e71d8d530055d70d8d530053e74d89530053d74d89530065f63d89530063e74d89530047d74d89530063d74d89530043d74d89530065f73d89530047d71d895300c7e70d89530047d74d85530047d72d855300c7e70d85530053e74985530053d74985530053e74185530053d74185530053e74181530053d74181530056e72181530056d721815300576711815300575711815300e3e74181530047d741815300e3d74181530043d741815300e6e72181530047d721815300e6d72181530046d721815300e7671181530047d711815300e7571181530047571181530063e64d50530063d64d50530047
  | 41 => 0x100000008005001c00c001000100080000014007002804d001802f000c0090008006000c0000004005002c0070014008003c000000001300080000024000003c0120068001000801e003c001000c00c0000003001400300fc0020028000001c026000400000240020008002004800b0050000001400d00600020034006001c003010c0010018000000c001000000b008c016000000e0010001001800f01900030000007000802900000000000001001802000d00420004009006800c001400e00040000020000000000d006000000140010004000000c00000180000014001003c0060040005000000200240310000001000001900d8013001800100740010000002003000000b0001008800f00440000008028004c00100000080018009000c0030014020003400300080040054003002c005000002a002402a000400000040210010004000804100140050014000000000000100010000009008c00000000070030004005c00e00e000000100000000000000000400f4023007000f009804c000400000380060000014001c00d000800000000060020003002801100000000050002000000400340000028013001c00100480300098009006000e00400020000036005400300080000004001000000100180080034000001000c005400c0000000000c000000000600b0003008c007000800a0010000002000a00100000014004001c03800240030000001000001a0000001000001b00000000000015002800d000c008000000200080250000005001800a000409f00100250054000001c001001c00c0088001000400200040000064001003c007003400c0044000001000500240050020024001c011000000e0098000000000101080000028000009001800000190004051008400000000010020001000400c000000a000801900040000010020001800100040230004001008403900400000014003003001d001c00800100010004007000000700240010004001000000b001801a001800000040070004001000402600080090000000000000000040060000008000000200140280008004000404b00c4009002c0020028007003801b001000600000100000008003800c0000005007400300d80010000002003c012005c0000008001003004500080030000001001400000400320050000003800400a4005004c00000140060010021004de7398b54004dd7398b540047f7258f540047f7158f5400c7c7058f540056e7218f540056d7218f540055e7398b540055d7398b540047f7358b540047f7158b5400c7c7058b540055e7318b540055d7318b540055e73d87540055d73d87540056e72d87540056d72d87540063d74587540047f73587540047f725875400c7c70587540047d73983540047d72983540047d71983540055e73183540055d731
  | 42 => 0x5001800c0000000000400b004c00100040030000000001400800e400300000270050005000000e000c0080034006000401f0010001000000000000000024006000c010000000300c800300000000000000000c01c0010000001800100080020034001001800200000040018007000000600040090004002006000000580060010004001400500000060000000001000302140030004000000000500500000018019001800001240000020000003c0030050007008001000200000008040001401f008400300000000010002002800401140000068031000000f00040000008000001c001000000100080000000008003c00100040030004000000404d006401b000401a000000300000000000002000800000940000000001000400e000000100000030004001002000500580000008002007400d002000200040000000000001000801700170000013002002a0000000000000800dc00b0000001000400300000000000001001002900000190024000001401700200050000000000000200040150000000001400200040270000000000803e029c04300140270004000003401a003400000840050008002001c0040114002002800200040000044001000c00700a0000006801e004400c001800400400070000016010000b000000600140010008000001002600040000000012001400200040190000008000000500340080000001000c008000000000840000034017000001a007c000002800b000c0000010000000c00e00080130000026000000400100180000001001400b0004006006000000e0004017c002001c00f000400c001c00000040000014022004401d002000000a401d000400400700060024005000c0060004002001c00c000800000100000060000000c0370064003000000e0094000000c00a00140000004007000000100100020000000005c00000080070000002007c00b000400500d40020000001002c0000008003000800500000020014007004c003000000902700000058015001c001001400100080000000001000000a001c0020000000000000100b802d001c017000800e00200010008005005c00000000a20004006002400100000110000005004000200040040010004000800800000100078000006001e001002f0000003000000300040010100006001400000040000034008001800a0008009004402b00180250004000006001300c80070004004004407800140000008003000801c000803800000000090009000000100c8001002002900b000800240010010000003800c001000000080040038002000000b00900000020003000000d000c0070000002000000c000c046001c009001003b004000b0054002001000000280070000001001c014001000100000020018003001c015004c001035000700000060
  | 43 => 0x300000000003c0050008011000000a0008000002c0010000000001800e002c000000400200200100000007001c00401e800700080000000012000c0020078000000000200080010000000004c0040000005003000d00980080038003001400b00b801200000060028001000c0210020001008800000000000000002004c00100000000000000000403b005c006004400000080040024011000401b003c000000000000000020060003000c0180028004000c000000401d000000c002800000380010000011000000c0020002005000d00300020000000000c009001400500240030008004001801c00300020014003001001100fc004001800b0004031000c0160000021001000200040010054010000c0000038008002400a000403600f0022006400a0024010002000000080040000000006c0050008038004800500000000010000000400000040070014007001c001005804d00040020090012000000c000800b0000000000c01e0068000004402f000401a0084003004c005000800000080030014022001c0010120002000400100200000018002001c000001c00700180020000004009c0060044008001000400080040000003001001d000c00a00000000054000003400000640000008025001400c002000600ac022004000f0010002002000300240020050003002c0050030006001c0000004001000000200340500008000000800b000401600880190000000000000000b400500200000000000002000b003800a0010001008800c0038000000000300380070000000000001f00000040014000006800000340140018007005800a0000043000c003005000d007c001000c00000400080000004000000b00000320098005000000100200000048009000c002000c02300040000050001001c000001c00800040170000019002c00c001002100000150010002000400200000070064000003003c000800c000c02c0060000004c000002c000000c010000c003001800000880180048000008000000480040000003000000100000040004001002c01700000000010035005800d0280002000c00400280010008000000400000000080050000000800300000020044005000401b01840010004011001c0020074004001400c000001e0024002001c015000000700600370004007000c0030000012005800200400080020000001c007005000200000000040008001c04f001c00300240040000000000c001003c040006000a0024002007000100000000000001000800000300010004006000c000006800300000020010005001400000080010024001005c0060028000000c005009c008000800200000200060011004c0390008000000800b0038000000400c000800000640020008013001800b00180020020001000000500000000008
  | 44 => 0x800000e0004000000600a000e003400100000180000002001800300000000008020003001000d003000140000000004006800100780050000000000c000005c027000000e00000000000008000400900240000000000001400700700050054002000000b000c00f0110002000000100200000018003000c00d0018000000000400040000004004004c00d0000007011c00300500020028014001001b004c00b0000000000000c0000006000c007000c03d010c03f0000005000c0000000001000000600ec01c0008000002c02e0000001006000000480060000003003800000980070008000005401c00340000024006000000000cc0090008000003001a005c00000000010000002005c0100010005002c01100000220004001001c00000680140008005003400100080080000003009801300000020010000000c005000401d00000090028000003c0060000000000000a00100040000010000800000000040000003003801800080020084000000006401bc00c0014007000c0080038004001800800200040014004001c000000c01a000800100c800200340040008000005000d00140000050006000001200140170044002003c00600000000028000000c0050004002009000500480000008002006c0010010000001400000a8000000c00200000060000004003c00700dc000000001c0034007001800400a800200240210004000000c00000000040000004006800000080040008001002c022000c002002c002002400000000190000002000000100400130038003000000a001800e00700010000000000400100100020004011001805f00100000014003007400200000000024021004c008003800500000100014006003c012000403100440010078001000000e0180009001c016001400000400000004012000c0080014021006405e0008004001c0140000004005c000000c00000a400000d000000000110000003000c00700600000064006004000100c00020080004001c003001c00600400040014002000800800100000000006000c008013c00800000000014004003c0000008016002000400600050058008006800f0000009002400200000070050000005c00100000000070004005000500000000020010000800c00000050008009000000d0000000000400000000000048002000c00200200020020019000000000d000e005400d00000050004001004c00b00040020000017000000d000c002001800100080000038007008c000000000500000000018000000c0000028000001400c004000100000000024000000c005004804a0088007000400200140230018092000001300c0012000400100200040004005000c020001c01300040100000032000000000040000020002001400100bc00100040020008024006c0030004000
  | 45 => 0xa05cae3c0351b207c72a34474149c2bab4121dba24602c9d9e28fa4de2690ed0cca1a328cc02d875e023e9eb36922eaad569e396286d40a6e34dabb44a82b8200015b45bf94e200000005ef8000c63870ed2a29c80000a4cd6e846cb11a3828c180001ea16a4af888540380944817b53627b02fc9450bf691c07e68760b247aeb384bfd9de86a7252200000004ac26aa60ab4cc0000000a7c2cdc858800011e32d4bb9277e9d4262e0ff8f662610e0251a96b6987218212e94145b1261e80c85c419e32c4cf58caec2fa0f00000000b07303a67a03de26da8b21ce3252d1986663f5000062797468129e98755902445180005f1800000000002c4800000012e200032905b6312e956119c9cea0f6ac30000724921caf736bc1a8a3fe0bb00000000b5263325ec00009fe12402f20002daa00036a4b2e12da0000f86cd880004a28cda00018fa41500003d235fe4108000ca3b578000024e323965c20900000000bee000000016300ae64b10b8508127c1f816ee9c105565df9db8d20884ca6722c42059ede80a9a868c11ec02fd098858f0ea6227b408c451264a578000119aa7400023aa0001652b8105b03fe8a84000277c6fda360a9800007a82f4204f85dc41d837600006de0240bf2253ad36630039e4bf000095d917eaf981ae661350050c2f0295f9d363efacc8a071cc0d4d04800ee85ac06c2410b1f964a72c8b1c3182b221828cba3bca6fc99a912421c000028a80005c8017e642813825014cecfc187c300833e5c48a2800020f29581878d6f022a38e825861781e0db0a77487435d25f6b6804e4114ca9113da00011ba8de041411bb022d7f0b66c20a1c40002f7c45726549e6a80e77835e4232ad72d30a14c84619d65eeb09600003125b211162a0299e94703c885b9ab07efa8746fc34241069700afd178e3542eeeb61938cc609c420002d4c9fb1e66bee0b16177a7306a128c6d9f92108af13763360000b09126ad8aad9e00036785d100007de00002640d168ab800000009eecda85fac93088a00009e00000a02727837283384e00e32b6831603f01750c980b9b33a0080000c71afbeda2197a3390000d560c564ab0f200002efc1c12804bdc10a436eb1929c62864d301774c901fb0323277831eb226578009839c185c4d81d8456322283a19f060002e5cae4a47c5e6a25ec358c540a78a3a41b837078a0c247d500060014002004401b004000e003c00200040030028000004c000003c0000040000001c006000c001002c0000008007000400f00000000000003000400a000c005000804100300000064000001c02300100000000002000c011000c0070000005004402e001c0000024021001c000001800200180070000001004c006001000100000360008002000801f004002e0004010000400000e40130054000000800100f
  | 46 => 0x7a4c08692f64b7133f8a831c5c7feacb0713305200000002839bc65ca0ce850ba5f8b968000b5d18009eb8000c7b8000d64889a965b6b8877000057326320002086000000000012a267d336c0000000cad000000010f4c132354ad3009e1969a0610a8f5a0000fccb450ed2cb1a86e618882200006c81958000cdd174c3419528a79b2ca5bc80009f9a2000000da64f600008c9073c00026a03c900247d7198c6f39e2c212089015c2c6812600006f803cab00145ea9c22c67439e6a4feae708f333cab53aace8df02162009dde4bd000000000000000000000306000024d400001e400011e20002c7a9c0000069f80004eea8780002eaa92909a69318000124800065b1b7ca8b2898d9600baa9500000003136345113082e000000000001df0564083acee5bdacccd7a97ec4d422be8a0b3406ad2d58d7e3356000187a2dc35dc97a268e5212a6a9f588620003320046a96c58480000001b3822b934e000126cce402b688fafa2000053007b89c842d25746049fc8cf69e78696945859c2af06ca2394b17952460f2060ad93144adb1ea67fca346be70d0a5ec8c26b9f2bfe5de9c1283583b236585e2049b6ac12d9f747e11b6c7df2372373abc86c28f9ec2429826b305f65c9207e583805091327642281cb6b7c8c348bc36ce0db264cc0e30eed2cb4d6539b2b8511a4a0d2f16988a5a6f263c20883aa352e64a86340002d8c0ca216c3aba260afb8f7673a1aa861a010e84f04ccc080208cb78ba05590000a2b21b000011a0d3e06aa000308e834061400000009222b7ecb4aa50bca0d82c939112cfb00009a480004609ac846528c00000bc0ba300004a0a8b600000006fd000098f8000bfeafbc0ff2712c12845016eb30000007423210266be088b031327960b284d60001a4e00007a463799e6b2691d88efb0185ae1a94b0b29f8b6a0aa2000230c99100003ea05380002f4a70e0eacb988f80000263600023b80002dc0000152c3950c300cd8908b5f091a3e72e3063d2294ae400009b607786141be8d4c2a043080000a3580004ad80005fdb00630c8d584b2004a0001bbe9181ef452c349cbe224ae0001afe803aadc924286a4298000d07018cb2881de8021f26aa7af1e494245ec8189f60001ecec56250e3598562955aaa69ca14ca01a8dae464a0ae856063c6c00fe2d5d9544b7812fe57791d45989adec673406a588b32b570efe0a1243871b0aaa3568eca88d227000418ae7428ffc07a80f07e08826a74a9c610300f80b1110c11c2922d7332ee8141f982f59c0648e9cd030ea5de7231b481ac0000205010876b0e669422d1cbfa2fb04be8c4a0f605c88508c4869b151e6d68af80e39b8ca80af9a4db19dc00026dc4619cf4bfd0d88ccd19369520a16b5033c496c311e45c9276c768fe6a34968a34091eaa9e203a15135e25b4934
  | 47 => 0xd494599a29e2a8f80a72abca5a836e00000fc1c9b366223ac6c467b51272581aa63800006f2a146a0e80000000000651a6b273d800000029dc5af000074115a40038000a65abc22c405a677222e29db86263439cd43bba1c88f5a03488c2cf220a2ffe6c3ac5a8ae075c5b3a31c5298b6c910a5280a98000000007c0002f8497f27989688fa40001e586e7ada276085a80000000a180b0052913527ab0dd2000000044f2b7600000000000000d8614de00035266740200ae20a4018890e6b68107800020ba000102800000000f418087e734385fc800000011c8457800050e2f080001a96a998a689e8b448496a952cf1a0eace2000049d0798867b178a51a4a6a4e9ce284f80000959b64d7bb2e89578f08bb89cae8361bf2c02a21a62c0000000155e000283400012ee15f952205833d812395ec00015d60000000c7ead42bab224ebeea336125170c2b58e58000335ac100c50aeb23e44a20000000303000030aa7ba87ee64b82fad13ad0a00021b477884449f41872a0fb3bc00000009c3116e08d92626729a8e000350400000008bc800000000000001ec2b30000051424fa8c980000002a900000000d079a1c0ce959c1e229a4ad8309e00001440000000000006600015e27138000479800053421521d1ab40426000023f158600027840001c8870535f0538053a777175ac9b80006eb19981fc8000000106058c86e4c79832c31880000709584bdf9832c9834868650bce00018f823c28ca95c07c8d46041827e326600007b4156a2869eca9540000000bce09be18a9b687f380006dd19781dc051a7309b6a218117856e8000837166e83e1ac29a5b1504a110f20000eceb4d101e270b2a0648b3b4ad1a1a806d05b289f953896c98be85103300410fc63908844ca6ab2e7d3ad3a8932ab200029a60b23216947abe45020000b2930ec000000059597d07c4856ed1aa9e0000109aca7ab9a2ce843200011aa1ec2a4c1d117c834e92964b627820edafc60000288c0780000000a3c4dc34547ad9ecad7ca9be600a91400000000000000dadb69a00015623ae1d1c2ec0000a15b056d43a8080000a6a5a48000c95800000006bcc7c80003978ebc6e70d6ac4f80008928f824a70a9e5b089468c292a668080008a7977043800000002bf00001eb40000000b578f0698500000000000b8a1ee2000267008408642928ed495b800062801347840b741b580000518fd267f0000493000000000008cba6acd0328260741bb8668000084d347800032be25badf40000cf4000348a3cb80003bd8000386000032f000000019ba6898000b420a2c03210648c03008000000618b09b004ab18c57a92061c300001f5ab667d5a63a99e85dac3380001bd02cc0001b9895329c000023486e5aeb06060000237b51c5a1327ccb88ac805bb6ae0000f78362800009
  | 48 => 0x39bb58000000000002910000104609080000000000c1e1f94a38295a0001c0a3da8000d6b25aa54384f625a0000be90000c89311cade1a08229acb2d3ba22c3f0800019ab6425f9a6ae93e045a3d296b027900a07ed2362b41208a8241e5c44aa12a4e8136eb009e9c0003626a7330428e40740641b37c66a0be450788c6d4e289250132d849184c2435368c9ea28da25f318666210923d48e302100ecc000259e0002a2e510a1f4a8cab0aa00aec205b1ae8a3f0000b8d316c0001c8a48a2fca09692a4974087eb458000056244ad23b0c405ab5c479ca340241197e079834eb86847629636a6301140215185800118000451157e0fb0a7282a34342e7b5a06542226ced8a44905053c4559de4d88b3deb2d0f280000e7e320b450b2b00005841fe0000031c00017504d69cd6298b23e73f26be8b40000b1100001b8ad3c54bacc6afab126565abd8340212200000000290000789b294000199a311234a4c5800047a00001aa0de41c20000000211a6108978000000078d000038f1c7e2850b9434a99406e886ce9ad800042780fa6ae33940000c062f80c94b8c80002f0a396000178c644a758321aad6c3c05ae2f8b56c0001e9224a99a6000000047b00006f5185200010083a2b5e83dc23c063d83d617583dc40b844021a0000119071817fb23222b00685a58000b061742654800000a8fae0d7b08c000123ec21ae1241f9ed89939fc40340a74000124015a2c12036106820a80003349f884000000beb1154708a02e6978bd80000058619927e40f2942782ab00000243a82000004ba1e8ca8f17d473332aa0010d7449280006ea883804da2181c890eac6d800017a8000a14b21e0001324337800000001f28d696549b080002940000b2f05e84c800007069dae8dba8aa0000e6c0000b820001a1400015e60000000a0b2ffc35b89fc1bb892200000002210000d182dee000166c4ff80006cd314e60b97ac4af86465e9937a352962232926000000c2a630b3fc87e868e4ff004e520b25e000225854c96205902a206ef1c36076805634913be6b10000bd4879c4f5069ea2b80007c20bbec7d84e40b516faa490aacb8e97a84df2acc2920c5a145895674f93d2af2a9585de0b2626b059021780c000000340002b8400028ea515a7227510b5eb2220fc40a9270b2180000210a3081d0f406181fb896f057a62d101ca5d8fa02a52ef67bb272abc3b0a04159386b5508bec60273cc0706b26ec80005d517382b09630881997c66500004b90e721a70000c302ea61fd977c1430000c5c80009c42a22310b670c772c2e66b2184ae908c20c3b162daeb61a57c047a364972c9729e704ed9dd07fa85f2a7f8b14023116a9f292f8cab162ed2531a07ec801e3fca0ec53ab16475812900000e2ed93a73200036c08b71122410344426eb044d1a0b
  | 49 => 0xf28a1d8000aa2a68887814a8d7daa9c78882d0c38018e69223f00000a8c00001f4bae081a0000e9825d0000cd433e05bd04f860d99040001f8e00023e80000000caf0cd0b74b49260b173204506d844e05606a807c6c8302960ab80b46e520be0000000000136aa8401c473fa7cc90b0eb200015a691e238e72c31386868db269c892e99c8bf8cf505e41a1ac56cb6a7b48718000000003e00006ec5560dca5db32280000e50cd29f768e90000000000000034c6bd735ca86aae5800033781aeae26bd609422e880001d8061a0700344bc40a22cfe8948ae28000b270e0a64c2c923422242d4a9f145c88e4a74ab5ecc78a92e9cb8000856800090810e46a980000001982bbe8954b70aab6acb246e24c944428495888b49d6c0efa8c4d0a15200d830fad1caed004c849c1328e8c3770c5e4348748a3ea0101e49f584bd89766a40790542140ccc0a2102ae12ecc091674948360210eacc4b29a160d2212565ad2bbc270345876327c6d4407d224522a431728a4459969c658a6467af03681668000000067cd531f20b88078c2b000000001ee849b98442a736b08cea3d23d1a4988fb144e13a2cd8b6032a29272e7e4b196ca1259d8e63528286f5822ebaf29880001cb82681df80002850102000077c800055e0000000000000000e40002d6c18c06bed9311ee607a14ad339ffe8ae96600df000032718b83e9927a76700006948a3487a8e36863108a9fc01ccb9a2e142de269437d15c23611fa82ac00000001576b3c2ae0a5c0000be3a21c8f70106b2a0000c1f00003d8131ecfdb0021fa0fec6b7129802532ba5ec068c4c89fd838117526408a24738066057213664f5b5623d507eca46000020cb17c0000306c43a07c00034b8a2f00007a20cdcba52fc800032802b6a5e04d8b1961741a760000f94000000098100000001a709e19592000163453520e480104746f7b2121578f1a330a9fc9cdaec47a3883ed958af0514800081497020000000b64000000000000000b7a3cc179223e311600000003c012944a18dbe0002bc48810000c6f00004368b403fe059e8fe071243329ac2b195307c598284049f3c68c0518000000047596c00000f12967021446da9ce57930f27f1805e6d9b596ca2b474bb98000d2c0692aeea3322f680dc00000009901b32000193c75500000002dce7c9000070d224000022ca7822e4a908a3103901b18a1ea91e847800098a0aeecd50000d4cb4e834e00000000deabbd1e4e4582554bdd11b084e18560001d6848483c27a786c49ac2dc6000283cc57343020329de9388178000304e1ab15268e8a04823930f60001e30d9680000000000000000000000008ff314c69a8972338800093ca21e0000000b4a0fc40001384c6293e40490000150adac000011c33c96506d50000bed13e24ef000066d2c380002b188
  | 50 => 0xb3d2292c6901a41c0a4e8633a7201edb16e61182f8293a7b617b13f8000094ac9b0958036820c134096200000005ed2d22bec85260001efe56503aa62e9a1e2bc831a4c2a4beba8b4be2b388aa3d3246cbc11b4e5a69c9cb76078a1ae2a6c22a20f467c8d9ebdca1328de85122cdab300001f2a4282af691e9292bd028feaf784fa1f936681fd11903c12e541a082a0867000000000000000278695000000001c85068f9089707684e99b1c0b01f688a383c00000adeb2db4ec732000091493688b323e2a82a9b85e82e50322017a002b1465af876cae887da73e32b6325a39e3f42d88838af5a8ce25b60fdac206d4ae661a6b6d647316e6b1498eaaf5ae1678721002949bba21197ee2a2867a6f702449888a1a73629ec03d862eb5a10c270cb5606d087dc101276cbeba78c6511606c1db1f409f20780d49a4017d19f0c52922657535988d40a0ab078bd2c7fa8e2289846a2cd36aac042d8e19405a267b33186b58b2c67e159086012b4a17b40a8062cd434321989101cbc0f9979cc1616de5a024e69d81a3485e2afcd59a5fe4cc9c70cbaa3169b925c2ac71aecb9d255a780352c18f924e9ef2f6ea15254a57383ce29f9a045bf1a0cbb6973e1109b92710074aae31204509acce00c978830db4e4d2912300fe0fb4421906a2a9b24a9a0856c5891180d819fa6440186ac9ca98e804b1c4a4a334e8e1050e4f008804009d12368831493d026ac9c28e857499c8b6e9134a538716d0c9ed6385807466d90383910de84521f306160cc418920a241e89daa02898a8b68000d669cec9dcaa060001ca800000005b80f96ce884a600019380001dfc0002ec0243222a408800045b00000002de291ca41e51b0d44997800084d800000000007dcb1e800032a617300007b90e88da2800040b0c4e473a2c000020daa6e90fcd4a0a66d068080a1f164cc669b707c606063472cbe07e2d488b927f803b032ea59b5900bbb3243832bf2bf8800097d1d9600000e2016b4fe7f7991a0892baed8fa2161e98000ae1a1d6571873e0002356db508c4da7213ac842b06baa2b726b921a6cf4234ed6c984cd1911a8d62291a3f200004f28000d97000000019ce0002c8a0002d32711000000002380ea04be000016400025dc9bab30c41282f612b19d86c0a74400036986360a60000348c14d9d9ac9d0e62ab8800090235d49d486fca16af7a3dd028606b000059f2e468d9a9e44fcb0ca18421747a01f0c89e8b04c6604deb202e84671add6bb31694d480de60baabb24690f0e5302d4690993f45702ed8a23a09a85a0e5a6450000572a60a23f80009f89e16bf6ac8e16f8000adc03eeccab5a6ba1ac0c000000076d137e8ec80007c88000be4108c88499eec1193064858000000125e3460abcb4aa00a7b49aaed16829000015be9700aec00013b09d68000a0d9
  | 51 => 0xa4ecc210e28a2085028ca2a622818fde92eae724ea322e00021a0ad68000a8d9f46a1080000000cfa1912ca06c50000a4c29d40000c124590aba276162c045a7709a7ad2423b26ee99d8b6e9ef852a3ef2a307f2a90a98313b25d3953c77623c22e1000092082aa54016ec20c08c0db40000621a584ce5b45cb2a8db43a5aa921b70000109a3b0b8a886c54eb62e8990eb440607cc33c2cf822900000000000000000015000000003404d6fb234659001635b02600000000954976618080004f200006a880002dd80000000000842a4022ea12cc4e510bc0000000c190f3ac8db2200d2971e501b2fc0001c7206daa98a278d109f1186ebf79c7853eb45652e81e8a4823c85b935565aa1fb622e867219783c409936d20e5056a92a8f5e77aa35ca8506323922464c42966a1cb077a89a983a87281fe830144840114801749eccbbb1d647a180000002a8c000000060528b469729c282b00009c680007cd26180001ab680a08d6c829b76772920e703905c0e280001cca308bf314f8775184ed6787b88bd9074b3b000094417d2000000094e000059a0292000137800011e087b000024fae0c254a0c800000000002948000000000034961480000aab8000000000000009b4a26800082c11d2c3f851002f022cc7aa88c7f9a47e3851f322aa218eae52d6e0b19e96b9107b29d3896a701033892128de663ab0e6b406d49b8aec68329c626c931540000feec2895a278695ee00003bc45d0000000198a6750000c1faa7600000001eb8cb60002af4b1c80000000000000341672914e446229c40000b420002bb0b35aaee21e1bd202732542d52a00000052e0001d760b7367444b98a2d72000000010528f80000395ae0a00034caad134363a700009e71ad417380dec7511045c9a5f6d53a05c808250ace020cc0002e0e57fa11200000000000000000238c03992809e98ee057f21500000fcea511f860002d2c3d1196e0d08cc000000000878dfc5712ff27b9800058e92ea69eafce48d0000db31ad8baf81d20002214d0f00000000000000000000018a84948000b6c9e447168000566994a2eb8ed8458a45a00036d800000007f00e1a0001888000188265d82c200000004658000000000000031f88280000d871d106c1a838cc99ddab9027d85c38b864201e4632a049a370944c7311aaa3f61e4c0e48a08bed901697602529199b22a97a6585d5b3709499dbc90d01302361d1665706748160a9ab1731cc0de8a5616f34f4a962dded99b630d00041c79800b67ef0bfacea8ea452834c8bd5955aab4b21c583149e4329a2c0c28bc868a812e4b498d04131d5a5cb8c908ba1a3aad5918ad9136625e082986580c9ebc59db2d7380b0271b32c73cad78000360e5fc14c2b08a6080fc9d4a35cada6a601b5c9460dd82b52b3c3501de667e9748c919502
  | 52 => 0x7e5b50ca4180000620cb437eabface91bb600018fe00000009b80000000000030380003488000271000075729e80001550b7f0000557000031d947cdb18000000101055388d299a1c3e51e2278c1c228ada80616be48000000261213fa9003a880000000ede5d8928e7561e0e00027027f500000002cfa3840d9c75d2a72d2b98962f9b38e00003406c42d5aad480000000ba41feb66a3eca79e44099ae8dfaf22a8eb5224cd18e88d080825861f7a2419a24a13a3c437b2fc061917e27079ba61b9906231c2eb28ea284c71ea042d2880540001bfa3d887100003660a6622a2477000000012780002a9a31b8204a76866238e09d40000000000194c13ab4f67a29af45ed8000904b4de00032d02cf2648b982a6e84ba986c4b066e0000000cc880001d98000b582a48b8721f2a4d8e600eba2685f3b440cc7327a00000002ca0000000000084a332e059b1949e930de0de1d989bda63000013e63fd0000ba68820000296099680925be20aa65a10a813891fe96933c8d882e2435e35d61009f3e53c80005eb91faaa0295c11780c2000052239a084e00024ea091b614249ae9eb260c6424092483bb2056bb70000000000033a8248000000062a8f500002df066c27e4b38a3fa10a212c85c2cfc000281a0001a108b080000000fe000026560000000a9f8000000000060907fe9b41fdc067aabac1788bc7b68000a1c800096b84aa0000f0c8031abcc7901e24fdb402950111089d1cda25e9d305058d3c72390e29980da0a0a9af281135f41d513544c9aaa06ca80765fa0220502a56aaf6a7d4af49084105a8863f29b4c0441a3849116024d025a02b32592949075045da1208e809bc48c87dea01aa6800491ac23400ceca1b07a8b61242a688b7228811c6b0eb06e40c9a281041ba02b10adc9631db685d8b447e8aac46f31ceeb4315ac168240e87924ce979257c90f9b825c18dd4b79b4d476a0d6422c800096981dccf0a0541bcb55c00034fa165a116d54a358d40b170685b264000095c4051a46000000000e1ea88cf240a0003248ba8239c3720d1248ba1fe974a67e555a236000147601b3410b629c989e409ae1c81894cd1282221d26da4c39d3892c0ab65418796645814a09528b87950aa006980009718184000000043593aa1a930cc00020b6ac20d1a16900002d28000bcc0c8a00013b80002e4e00016a2d1d978600011260bc2ae6b93249e0a52ab0c8f0c109c7115a2221c268fbae78773263cb49825c0000a047a408dac03920c81b31225d782ba469891c72b004020006c07522f12ce70000adb8000299304824a07d075c25020001934353973a9ce28f4740943ec0ca5826098ad208a32ae1e5357a23c800055ca43c0001970450943c4ce8000da0a474b6fb694c6d217ab042f183bf24fe000321a75fade895880002ac80009c2
  | 53 => 0x81c9ac1a1bda10f836471db17a0258b7e1661ba809e9d340f4a496ceb1cba29198d294c1a209508500cb5ac3078aab3e3a4933ea129f38297852c6479da4798a6b4cb9990c5810ccab792f6885c8d1ea4f0df0000109c77f8000d8f28c2aa9032431ab10c1bda0e09d99678cdeae8e000176a43e89e24428000000000000028841b2966652f0000000206e02280006b80dc4b6c0000bd4285ca650bb47ac893a79400027141aea88e8c4021daf265552ed4b650d8067f8000000246ab6603b433b8e124d1a08271633926b4b3ea2d604ec0002f6a371a53e39ea02c40f94f49fc800020e893c90300000f90ff040d105aad79956c38969e3e21900000208e0003050b9ba4286c217e497a820a8f784c612780bec2d9fcc19da9fac8e2a380000000190b690b0f8014781239a74f1f5a03bacd06d01f0a7d8b01acb70eb626627b8cce03162be80000fe875a239b01428333b2a432e3ec4a800000002b200000009b98000000292c031b4fc6670436c6a8000c168000d49286810f1dc62ed9a7c0000f1690689b2000000064f800000031d8966000066e2c8c0002db41ad000088ba49a8f685b87991afa93d800054607aa29083888538d5e2d684d40001600c3704ae2a0800000026c62c1894cbb48000b442b8e00016e8a5f8850cf01c30d74000000025c41b400000b90d560848d5456c12d486db0d0b5f9c5e8a0284469602f4d82040e56e2bec287aad85ab0b8a7dbb2023bd1840d09b11a7949ff8bb5aef2000188aa339764000000015d217cd29a01e17e2e6cd34027226320d4c582222c4e95a02a4945ab0582d26801704bd189a27398a2e1cd206432f87288ad0e8078c8de09231faec2a00ea6de35d8aff308a7fc0bc6bc313a2431b4420130000ba912e643633e24fb8c7ca3522a89e235426fbb6be050a740692a1ded92139e358971ab37a8c8b6b89d271f0e4685a9bb4d03943a0020c1c054a754792b3e8b59b46e89113ec26a1caa78f0b8c528a3920031118643a8e46b881d4cfca36acaa259a8a718dc30281984a7b44c21980007bf0c08cb0a0848b3b586000336e8eba550c91087200020b400026840002c3c46d0000c2d135c3c89da6566218a7469908ab010a200010580930000d9eaecedb72afa000130800000006d183a000021b200019260002fc4c3aaba600015d03b9013ab4e000039d3152b752992c1d1a889b302e224c2b242e72c36089ae9c4549f9000002066678d7e000051c55ea5da0e000006a0000000000000c98000000335e41ca1d26262d626d63540000000055a00d6b4191c000013ac4bcaa5c2c0a4b2606800000031e089980007c41c8471b8000111a3763632f1c55b222446f0e00af50e2613cadf84b43230000365e0001f500000f9aa4d0028000195400b00009b00b2acc78000000095a378ace44801a6
  | 54 => 0xf0b8016169f70e823fa1f5eae7a5883398fac4aba1885091e5a62b2b28af3842060e128cbe30c3c220858234831a8db2aac201f852494482305f72a409468ec4bcd2f1a9f4884287c29122840000ad08000134860e00010febf0afd414182a2c9e1a8cdb6840009c235e37d8000cb30000000000000002d60002c1a00013b41a22c063df82deac6a8460002ade6a7ad440000000c199cde59db24263b01b8000325ad94a9325442c348989ed05fe00000b3af249948dfe83f846093933589c581ba058a20e000294ac83ad5200025460000000000000032c844c01c1c82000268c3ba8000d890000cd180006e214981b6800000000000000000bb780000ae0fdada5806405384fc748ac64690abf600013e89603000d8a228ca05099a7199dc400000005ff800089f14b8864a41c3700a3287a000084c0e8488816ba4632454a612d20524169006a355e6998f681ceb4465f304da5aa913a0a026421c686684e098485e105284b386801fc35fad6c07566f61e9a5258000c59a2ecb7300000002c261e091e449c8a7600014f000025ba71a034834c180679b2ba0c2685049d1a60e980a3d05ea804470e84589091a6e152994ecc4a9ca57e0a7c5152534000042cb61274a377988e82615f623a0afc30b8000ba608860002b747000b1a95732e08c6976eb1e17d80002c4ab140000b81800007d8000ad3ac08c290eba15d8694257a3b61dca6ce00000002d324760000000c7409f0b6e27fcc0593042c82c62518290e96d08dc4c081cacf9acf638c8bcab66b26218100002608000216908e0448fd619500000000000000000000001920002c840001cdc000000000008b6000189c37b9214ac5ae9200000005000d68a0c00003b6acba2c6000088f000085fb676878800031d0ef017c0060986a2fa0001f7e000122236f1e7a4dc800011f8c0c471210e04828f21700000519048c000336068619c069e000097b95aa7c0000000005484669b4aa4a981c2cf891e1078000000000000017b800029f200000003768db608d279251032a48cd3686b05333280c2e882b82ae49e81f9a1128000b9a80001ba8000d800000cefa7eac2213646399fc22c2b5740c001682a201ec829b43a4e205fc11caf14cc524bc11493ae18e2ce87db31be6509542000164800003467d827da6b00ffe3e61e40c248caa09b00005468d7644b0e3e7dc26d46c68df840999243ee36367062cc22b9a30e0001d920000000b823508d7789d03c7af6cd210000331af6647d95701882ef073eb3ae7aa9e826292076417b60ac2611063cd1432117106c6d78f7c5f02af23669b864ce0c9a9892c4e6d81da044f9082882a8dc85708d445f26ca7b817a2d31101a8ac30545ef16383531dec2ad11201650c2850d2e103b1b61061d07ac2e035b88ba9bb0335b0d8272b68e9882e644b
  | 55 => 0x607806f0a75c277a58600023440000e084cc134c0002fd000000000d7000090b995a0b82040000000007f0cb8b101dee6e3800090dad30470aee814200009d080007cb29a065790b2c2e15148fab5485ac8b46000064cd8797fcc679fe200c160a60326a24b10000a08314000000009162eca300322212c0000000286c95921084030d2e70200009ec0304000139aabb351e1122f0a992857c94b0e244302fd6d36032a9330f180002b324ae09862012a52000000000001d852680003db08b46b1828e7578b887d031846601fac8ed03e8000291c3b23102d5c922c3d92eae19900001620f0a7a519e00f8961aa5d0ebe00020c2a8216369da00009ea8000248000000010b00000000032a52e0002c0e0002678000000083e8000a16000052ba58e6b99c1c4c684063e4a8be00030fcb3ab2ec4c60e94b77201a6ceb0285d833f4b5d83b8af1ac320002e80acd8f105128fdc8f9872a74b9f367ab94aa5fd294c062b292244196ad2e861c12c82b444700002ff000050ab1f09a010d041f28a2153000050a0000c942d18000077e94134dac5d9266b19930006590ee8c822542170000d201d8600035b602b0bfecd213369238c2caed97908e1801a1ab821cc349b849b131ae81198841e78000a9293ea08606524fc0aa4cbe00000001a360000000aea8000338294000004a0d8b0db854f90be99d1aeebb808960002964cff80005d29472cd49f6634d2a8e00b97ca0001be278fa8a8a102cca12e08360000c6c132015400010aa172973070a147056d9b1e770939652b1cea018a6de98a86fed9b2d707540cec0002f2eb87b58a46babcc0af22561f2a4b89eea80c163b0f815720d26011ed4b5e8684cec00008a827c009a31422fc26064820140a398456202b56a84099cc97e83667eeb0805580d46ca11392b1516f0b6f000056b80005dcb58ebe02be800024044f084c4b182374964343e0000e4eaa8a816b3487f8be59ff638a80004ca13de10d1ec6ba081860000000c70338c0000c7814291be48f23bc1e813dc5430000a6b819abe9a890c401708000342e0000000000244eb90987611f29386940000c5a96cc0001fd000000002ab80000000f84000180ea63183ec800e2cd17a1c20003570554a776d2b00000000000c0f239859390ce79586902460b64a8591327be26a4d051796b120ad039700000889be4d0b1a9a3cf0c22ab221d4c0daa8800000000000000b4f9c242968e7600014dca8a97c4922a7ee000184a477800022700000002f5492d36a2000303e22480b8000000000000000000ccea5bb1d60001d0ccbf828a0000f7a70b12a8a3300004b08000c1c9d7a8c505aa6e40ca045a2c7ca6c1a680002888b4784825a09512bc82a129c782503248000b8b800055d1184ac50358ce7af321ba30f463200007759a3cc318dac9942f
  | 56 => 0x6c624b2072238b42a79a0ae4d46a99a00022e65311ea4ae61d90000000000024da00000002fa941275493486658966cc6a01600013ce21631ba2448042a280000000272658aaf36ce28e1e13604a85e7a2d4a90a57884330b0bf610e84878628c48051ecc1a58a0001c6a8e000009fd135e4f30d5cdaa0000000044e00005c2c4c2adaa19a82e159800076e8000c18840a20210dc00000005a38000267000059e89b8bd1000032b2a469a41758ad70000d6d0000a422c28000226e7749d1860d22b6000149250b1bfc00026febd21c0200d8b0c43e309c57e871e57d25e610911ca0001f4a000003a26780000000000aba86c600024ac0000276000140eace800037426e8000035082f24ca56a1c568b5800000000005c282e8bf91be63db800027d2efe7ff2dda51fa32c00036c4797800042e9bd000007d89121890ccf932a52d8970d1f01d6691030200000000001f444b28000712a53227e800065d21ee245a904da7b0ac305b35c9722a861cb84e645e80000000c14d061ca663bae36d61130c8258176d1e886e9d7af2cd510b1e4e90f2a12d06d2b0294228ab1ca29a1948cd5a24dc52232c0d2d8000000316876533d25b70774c7b0000943330e81e9f8a97597d6cf39cca2cb9b563ec2cfe9aa2f3a4e0272c75b870a8a40ec03dc83560ab163ec39a66c934b2f263c81286e906362b898c422e06cc2bf8ae845c1dbe3c721bc0c7853e6ac866ccc10cc8a4fae528c608fa19f823c0000000af027086bc0e34192000000000007531d200001d280001afc000234c0000000167000000000000000000bdda1e6000146ecdc8000aca800073c24a8870000000000004bc000053b1776cbd8000a3d8d7ab9d8c187e910709991b16cbd2cda0001da29249f52008a880d5fb1fc6930000be7886a055ae56751a6f8d3800000e080000000a982f4000076c0000048b22c000000096e048676a95803b9a2ee000297c0001a12ace021a0000000b648000000000000025d400028ec43221ce0001794a9e81a00d308e00000000bbe079a2bd874e0001cc678e2c0400000009b200000cf000071903a257600009340b480001ace02233640988000a04287e9c912360000fc0c850000638ae7a7cb89ce542b53a4f1897e53b9bec0000000afe0000468800000026664e38b385528b8e000280042d961c5a1807a9c3b02cd6a80002e61548d55000014ca2766cb35c2d38824a02a9e6e0001df436a23a62638cd45c427e07a11ebe3d7277a1ad871c3b0a4c81ef865c07387ea0e5b1ca7623368928b4626e0333661c187ec69ac9084730ba8eb00004cf0bb20000b560000000a6f00000002202a86800000000001831aac4082dc800000003a6a53a25416d003ca2aabfb3422648337662c80a2671089824d19320002dfa3b7306aa5c8000b6d80005f801c6a
  | 57 => 0x42b1dce2e4aad06cc000000021da00008ce0000d90c4100005f790489418b9012926109ffb39a7ce8334000008e9b58000203ac6ec5d19180a09a6229ea8d800000004cb8ee82c39c2a9da83868730488225000000032886dc817c8c7b106d24269cce802a8121114e5608000000000000000000002b26068a7c8b1d9b3cbe62d500000170b258000314964272f80004f1356ed689b12375b1b23e280001863634d71af62532329c3be32c8437a5acbc012585472110d28148e6201958c44a3123cd8df25cf34d22bd2298060323a0000faa68295bc8270bc4c64246235223ba674ace004f353c6a91b0c29c11f85820cb000017180002950118b67c0002812bcab094ba5920ab1d1398000269ab10a73e09bad000002b208231f4c15c910e1781fe43730000c032fe07d91c46b4b8000d41a748a8900001be800051d12de15e07d4c4d00008db000000015660001fee813abbe000201450db1483c99fa01e3800055f05d87beb0d429e25000001b4400007005c5000000019b2b741202695800070f33307eaa1ae75f2368d8495da8bd1eeeade9ec482499debd32f860d6800003f9688a9920628d918547598000d9ba9a872d0000b13063a000364000000000000000000000000002da6b2b2042eb00000001f80855b47e00016ae53f9128bad16729510000000000080d918e1a827fac7780006440b68be500009bc0c72b5921f69bb2a288f3b65495390f0635800074000002f3000000021fc0000724000015a000019c00015b200034982071bc86afb4aa00031080af8f56ac489e864e80005500a18a8f80009b49a74aaa87307252bb833e0d7c608188c13d2caec4c864a0c8000000008cc00004bc00002a46ff98ca8312024000330aad41dc02159f0e5faa9e24aab5e01f1005c08e8000c5fa9eea6aa27200002321e10a965cd9d4034f956e7032a1cd6a075e1289312ca30b7c00004dc5da20de00003da46c9310c440b6ad39b026b67012c000300457c92685b5aac69ae0f0200000008a1067000024d693119aac322ba80e615dcd811a0ed79b3861718592026985a01cace67490f1443d967e34103f4825275634b10662e980009fa00000000e4c3e380000001044a6d8608bea9658cb91f1a6d8a2feb7aae187fd28962e58150a12181667918100002968000238800021400000000c568786a3b843845019be92da3f66a4ae3879226ba44214d639e202688e0000800870698b25be8ac999228d86a6ad207588019e0651e893880fb5465b50a867d214da00032086fe27347122afe1f000006369cce0000000a6408ead65099254580006de837e0000f42000349e8940412d859e7c95a1bea052270698d265c39aae2c98e12c08dc2bd04dd0534c9ab4f290c30da99ba0c6a091b3e1bc0202c559d1e53492548c0b56491709e633f83ac5251
  | 58 => 0x89aa9e02446361b0121553638841848aadf23221f0a03895c9f427da941c17991983888b08be827947c7a486489096c7a89c900002d028be2e020000f4ea7dab04d8c80004f829566dba3d8187b46cc2ca06a20401be000152abcf18a647f191c1a29a98350b0a6bf732b031180007861ce49d88000bfb98921c52dca009b58c00025361be215e2fa125c9a6297acfb829a69912d6000084aa2e9e240478eaa413a9d00dd0aca7509eb06b6afe600022526c100000e9121ac62261600000006268e90065100e8caa18624389f20000db0bfe337ec4a344ac709e761ddac8200005505978000bd7968c8551948d4f8a1ca93905048e12bc2af922ad92a1f85911c549252be00fa94629bd246865981fad940e8ed5280a643b1e2e5361f92bb21e127bc900668faacaaab33b85318a6c827aad45d735aec0d357c5629e3a86b2b1ebd807ba718178a042887a7bda5f07b221041e8a01c00000000121b264aeac2a998b124000055286e29b25918d320a31a2e00028940000558000076aad299ea9141e1e3ac0b6000018fccf92e8a0000bbc8a211500001af81ff1d725d00000014b1c85cd27f685230e800024c21b0b50a0c30000319950436aa42a228800047c8e9e00000000002a820f81f049f3a1265b6b3cc425064e3b8807871d000031a0b5cbde158eb163268db7a16440eadf609d11f00e4334c35c35c00000c1eaba0764cc202fe21f0f320ec2af84c510ae0e9b258b979f02a3422de2f71c203b5af3e4562abea45b3a867db0bc0000736c970190a968d600002714d3a90887f48d940f306e0d1c09ea77d8ea0a9f129aa6d2dec749a5cc6088000a29a5f2000154c0da80003be80d2000000055181020000308bd3afa8000286200004220c89d4eae004ee0000000688800074197c2ae72ab89f78b9a00034f01d8a3f2a75a1660000000162b2ce6cb948a3330c3853a0bba8f505b486eac9480f33dc2078bde39489942ee19da79088f6ada9220161810c1a60fba73494b4000000015380001f8b1b8000000078534dc4241bc054d92600001fda5041df000008c8cc5a8b084509d68fd1c2e54d114a3691edc82c8fe4b60888c585134407c2a84c86327688cac7095b039ca078e644d08d983299f9ed60861242584c08921d806a08924a49a7c2ca614186a28000c0ba4809360b3020f2d4a62dad6a3cf8996ad632f078823529d31ef01ef0000000000079f99e2c4f1ca0661a0687ae327e34986004b70fb620b0818c1b0d528cf9798145329640c32b202a36460330000000000086580000e103549a9ab628f188120000000d67159e363800006f00009159c864f40018a1c0834a86001cbada416c1736b4bf4800039f1baec6c268aaad0a0061b2eeaca080f400000000002eba000138a5b88468a0cb34200025a81d300006640e1c9650000
  | 59 => 0x3fdb63aacd290247d24e0dac88ee381a6bcb44a4eeae5932c00035500ccb60cc6b14f6a8389cc00021a200000009be800093f0964000135880896a000000000000a9060c165a2970c800609d14b46ae90ce0b1ce6df96268399b8a190000094f3664883039abc1a05acbe9356000000024db15e1a58000ac433100001b362772a2683a000010c29f48bf240600019bc3e8800004010c432889800f180001338a5447699c28292f8ab27827e81c24f091133ba000111aa87a1900001fd674c858494ab1a230f808600035160900454b888000896806e4c7031800014fc6f12d96d2d0174ce603d490c94be000014c000288a000000033d956a77e80002fb289c000000006ca124ad50fea762a04c6ae9c102400000ce9afea1f39e022d400001d4882e639229ad080000214a2e074e9fe8a5e1e36a7a88060ac2a9652c803c7fb1e0c5ba96a6959a8f04028960720257a8820a380000000000000075a815eaa5000048618c6000351489b1d2c2c8961e00000003068000000015c0000b62000000000036c80000e204451664000192817bb33cd14b22a8e280c46690000a760a8e6bd997200024186e68f583ce30c2c4617fa8f2a98a0000ad85c5980aac0800003a06584ac971c0001d088b21486d56a5e2b921f8c3cb0f8c86695e886f831040d842e44db5dab4385b690014cc79d14680d898bc5caa2a670591b8a9597a423d139c519b49a13c0118c390e0e758b02a989a5ce242b5a483ba67cd9c8cfcb691780447b0ae0000d28aaa000031fac6ada12dfec749c52517000000020662d3
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc1d7418f524400149b0431ea4880061d21971d49100062a31ae3a92200083d841d9524400149b0431aa4880028761065cc91000526c16ca9922000a1d84195324400149b0432a64880023321d624c91000546422c4992200085c865cf51440010bf0fb1ea2880021761c63d451000526c10c7a8a2000a4d8218d51440012b306382a2880025a60870545100061b420eca8a2000c35841d9514400168b0431aa2880024d61372545100062a3b664a8a2000a54864c951440018a8ec992a288002d460c7054510005b0c10e0a8a200083d87197414400113b0e31e8288002a360863d05100051a432a3a0a2000b3080547414400158b0431c82880020f61c655051000546c10c6a0a2000a3686d45414400162b07a8a82880038518f515051000599406a2a0a2000a34865454144001c28c6a8a82880061d219755051000cb8402eaa0a2000a3686d514144001c2ea831a828800385550635051000562c10c6a0a2000a9683dd9414400146d0d3aa8288002c560e755051000592c14eaa0a2000b32809d541440014690cbaa8288002cc20175505100054b41cc6a0a2000aa58218d4144001c2eca31a8288003851946350510005c2c10c6a0a2000c968718d414400192b0e31a828800385a1463505100070ac28c6a0a2000e167518d4144001c2aea31a8288003a1a0863505100054ac10c6a0a2000e858218d414400150b0431a8288003a460063505100051b436a6a0a2000e1463d4d41440014690ca9a82880038518d53505100045a43ac4a0a2000a9483589414400126b0fa9282880038518f52505100070a31aa4a0a2000a9486cc941440015290c9928288003a1589325051000698baee0a0a2000b91831c14144001743043828288003255d0638c5100052a432a718a2001874865d531440030e90cbaa42880020f612769411000c3ac0ced2822000a4d8218e504400186ceca0ca0880038518d41941100042fc3ec62822000c1d74d8c50440010bb0e318a088003075d0631411000526c10c62822000c4f635c85044001898c6b90a08800315d8d71141100062a31ae2282200093587504504400186ceca08a088003455cd41141100070a31a822822000d257250450440016a706a8c6088003a418d418c1100062c3b2a69822000cb0765053044001e22a6a0a6088002d4615314c110007a0992a29022000f21525052044001f0264a0a4088002d861521481100041ec26e4b28200085d83dc5650400107b093acc4080028b612759881000516c24eab10200083d84ddb520400107f0cba6a4080020f61e64d48100041ec3ac9a902000c1d7498f520400183ae8b1ea4080030b5d262d481000616ba2c5a90200085d839d6610400183cc8b9ea2080030759173d44100042ec3cc7a88200085d8758f510400189ae7316a208003135cd62d4410
  | 1 => 0x30aa128090003321d9325012000784aa264a02400083d84dc965080010bb07b8aca100020f61275988200041ec3cc9a90400083d87593520800183ae931ea410003075d163d48200042ec1ceb3084000a55839d6610800146b09a94c2100029560e75584200051ac26a4b08400085d83ddb51080010bf0cb9ea2100030799173d44200060eb22e7a88400085d8798f51080010bb0eb1ea210003155ce61d44200062ab9ac3a88400085f825ce65c40018aae738ccb880020f613725971000466c14e73262000a1d8399664c400151b0539cc9880028760e65593100050ec1ceab262000a2d829d564c40010bb07bb6a9880021b60b76d53100061ab22e3aa6200085d83dd954c400186ac8b8ea788002936086354f100042ec1cebb16200083d849d662c400107b09bb6a5880021760f76d4b100041fc32e9a96200083d8799352c400107b0eb26a5880021760f7654b100042ec3ccb996200089d8799332c40010bb0f32a65880030799173d47100060eb22e7a8e200095583dd951c400126b09b92a3880028760e65d07100050ec1ccaa0e2000b1583d4541c400152d0732283880028d61b54507100051bc32a8a0e2000a9683dd941c400146b0d3aa8388002c560e755071000592c14eaa0e2000a37865d541c400162b0732a8388002a960863507100051ac36a6a0e2000a378654d41c4001c28c6a9a83880024d61f525071000742b1264a0e2000e85644c921c400107b0f320a1880030799173143100060eb22e62862000c2e645c850c400185ac8b90a1880030d99171143100061ab22e228620009358750450c4001a2ae6a08a188003495c941143100041fc22e5b2c200085f825cc658400189d06b90cb080031360d721961000c1e43ac8aa4200185c8758d538400107b093acc5080021760c7558a1000c3643ac4a94200085d87197328400143b0832e65080029360865cca1000526c16ca994200085d87195328400143b0832a650800293608654ca1000546422c49942000a1d83197418400145b0432e83080028760c655061000516c10caa0c200083f845cb654400107f02ba0ca880030d9d171195100061aba2e232a20008cd829ce64440030e90cb8ea8880020f21d645511000516412c8aa22000a1d84197634400143b083aec6880029560475d8d100050ec20ca31a2000c4f655c86344001898cab90c688002a56067418d10006273aae431a2000c4d755c8634400191ce8b90c688003235d17218d100062742ae431a2000c4d855c8634400189ea8b90c688003135517218d1000662b92e231a2000c59755c06344001932e8b80c688003325c97018d1000668b8ae031a200083d841db534400149b0431ea6880061d21971d4d100041ec20eca9a2000a4d8218d534400107b093acc4880020f61076d49100060eba6c7a922000
  | 2 => 0xd721952000626b9ae432a4000a1d83197644800143b063aec8900028b60875d91200050ec18ca3224000c37655c46448001868cab88c890002a360a73191200061b3aae23224000c35755c4644800192ce6b88c890003255cd711912000652b92e23224000c36855c4644800186b0ab88c8900030e5d570191200064cb9ae03224000ca9725c06448001962e2b80c8900021760c76d51200051ac08c9aa2400186c865cb544800185ec8b96a8900021760c76551200051ac08c8aa240008b5819d2634800146b02326a6900061b21972d4d200051ac08c8a9a400085c8758d53480014a902b1aa6900020f21974d49200041fc3ec9a92400083d87193524800146b02326a4900028d60464549200049cc20e0a924000971811c1524800189d063b2a4900031360c765492000592c08c8a92400094d83dc5524800165308382a490002d8604705492000516432a92124000c8c645ce42480030d90cbaa84900021761c65cc9200044ec38c99924000a958119332480014990ca966490002d220152cc92000552c08c9192400085d87195324800152b02322649000293a1b524c92000586c26a49924000e0c64d4932480014990ca92649000383191524c92000c36432ea9924001968805d5324800154b02322649000293a1b534c92000706326a69924000e0c6454d324800151d09bb2649000293a1a754c92000586c24ea9924000b45819d53248001695013aa649000293219754c920005a4402ea9924000a8e84991324800158b02322649000383d94644c92000706328c89924000b8581191324800191d0e32264900032361c644c92000707428c89924000e0d851913248001c1cea3226490003835d4644c92000743408c89924000a8d811913248001d0b023226490002a1604644c92000744c00c89924000a4e86d513248001c18c9aa2649000293219544c92000706322a89924000d4975dc13248001713083826490002f0604704c9200042ec18eda8a4000a3581193514800183ec8b9ea2900030719173d452000616322e5a8a400094d874cb5148001c18c8996a2900021760c76545200051ac08c8a8a4000e0c644c9514800143b0632e82900028b21952d0520006463b265a0a4000a3581d95414800143b0632a82900028d604655052000516432a4a0a4000c2c765494148001918ec99282900061b21975485200042ec1ced282400186d829da504800146b02324a090003139d932941200070632265282400083f87d90504800107b0e320a0900028d60464141200060fb22e62824000c1c645cc504800185ec8b90a0900030b1917214120004a6c3a642824000c4e764c85048001a1ae8990a0900038319132141200061bb22e22824000c34645c45048001a8a64b88a090002cae11529012000744322652024000c3876551404800165
  | 3 => 0x418c6000e1765504318c001b0ae4a08631800316d95700c630006c8a0ae018c600083f845cb654c0010db043b6a8980061721973d5130004b8c08e0a9a600091d84dc9534c0010bd0db8aa698002d46047054d3000c2e432eaa1a600083d841db524c0010bb0e32e64980029360865cc93000c2e432ea9926000c4d535c8614c0014390ca9e82980028721953505300058bc0aa6a0a6000e1553185414c00154b0430a8298003259d941cc53000c2e432ea98a600185d839da504c00107b09b92ca180020f612759883000516c24eb3106000a2d849d5620c00107b09bb6a4180020fe1974d48300041ec3cc9a90600083d87593520c00185ae9316a4180030b5d162d48300051ac26a53086000a3584d49610c00183cc8b9ea2180030759173d443000626b9cc5a886000c4d7358b510c0018aae730ea218003155cd61d44300042ec36e6a886000c1d64dcd510c00189ee6b12a21800315dcd615443000626b2ae41886000c8d645c8310c00198ae4b086218002a5619410c4300070ab2a821886000d8572504310c001d0ac4a08621800316595700c4300064cb22e01886000cc9625c0310c001b2282b8062180020fe05749972000616ba4e532e400085d83dc565c800146b02322a9900022d6067498f200050ec24cb31e4000a95819d263c800143b0932ac790002876127558f200052ac0ceab1e4000a4d82d5163c800107b09bb6a7900021d60776d4f2000626b1ae5a9e400083d84dd953c800183ae931ea590003075d163d4b2000496c26eca96400094d83dc552c800143b0932e659000287612654cb2000586c26a49964000a8e8498d32c800149b0da9a659000293e19534cb2000547426ec9964000a4d869d532c800161b093aa6590002d1606754cb2000527c32ea9964000b0d8499532c800158b0232265900029361b544cb2000527c32a89964000e0c6455132c80010bb073acc3900020f61376d47200042ec1eeda8e400085f865cf51c80010bb0f31ea3900021761d63d4720004a6c3a65a8e400083d84dd951c800107b0f32e83900022761e63d07200041ec3ccaa0e4000e853258541c8001d0ac6a0a43900021761e63143200060eba4c62864000c1d7458c50c800189cc6b90a1900031358d7214320004a6c3a642864000d0d744c850c80018acc6b88a1900031558d7114320006a2992e2286400085f835c7658800107f02ba0cb100030da1171196200061ac22e232c400183c8759154880030b90eb1aa7100028761065cca200052ac08cb9944000a1d8419532880014ab0232a65100021760e75986200041ec20eab0c400083d87197418800143b0632e83100028d60465d06200051ac0ecaa0c400083d87195418800143b0632a83100028d60465506200054a41ac2a0c400085f835c765480010bf04b98ca90003139c
  | 4 => 0x11400186ce8b0842280030d5d161084500062b39ac2108a000c557358421140038e4e0b0842280030e59170084500062cb1ae0108a000c69625c021140018e2c2b8042280021760f71597400048ec1ee2aa68000a4d8299532d000149f04b2a65a0002c3e09544cb400051bc0aa8b0e800085d83ddb51d00010db05bb6a3a00028d60665507400051bc0acaa0e800085f835c765900010bf04b98cb2000313a0d721964000626c1ae432c8000c35845c465900010bb063aac5200020f61f6510a400061bb2ae22148000c3b655c042900010bb0e32e65200029360865cca400052ac08cb9948000a4d82d9532900010bb0e32a652000293608654ca400052ac08ca9948000e0f65109329000170b022126520002e2600424ca400042ec1ceb30c80008cd821cd619000107b0e32e83200028760c65d064000516c10cba0c8000a3581197419000146b03b2a83200028760c655064000516c10caa0c8000a3581195419000152906b0a832000217e0d71d9540004b4c10e0aa2800083e86dc9545000123b07b8aa8a0002ca60870551400043ac08eda9a800183c865d5435000186aa8b88c4a00060f21975509400050e432a99928000a1c86551325000161f04aa264a000383550624c94000562c08c49928000a8e86d0932500010bb063b6a2a00020f61c65d05400051ac08cba0a800183c865d5415000307b093b4a0a00021760f71594400060eba4c7a908000c1d7458f521000185ae9316a4200030b5d162d48400041ec36e8a908000c1f7458d521000185ee8b12a4200030d59571108400064ab1ae22108000ca5625c44210001872cab8084200032658d701084000646bb0849908000e0d65109321000170b022126420002e2600424c8400042ec1ceb3088000a55839d6611000146b09a94c2200029560e75584400051ac26a4b088000a3784549611000156300212c220003a110932584400042ec1eeda88800085f865cf51100010bb0f31ea2200021761d63d444000626b9cc5a888000c4d7358b51100018aae730ea220003155cd61d44400041ec26e4b2e600091d84dc953cc00149f04a9ac5980020f61376d4b300043ac0eeda966000a4d8299532cc00149f04b2a65980028d60665507300051bc0acaa0e6000b178154d41cc00107f08b96cb180020fe05741963000626c1ae432c6000c36845c4658c00186b08b88cb180060f21d64552300041ec24eb31460008b5811d1628c0010bb0e32e65180028761065cca3000526c10cb9946000a5581197328c00149b05b2a651800287610654ca3000526c10ca9946000a5581195328c00151908b1265180020f61075586300041ec38cba0c6000a2d82197418c00146b0232e83180028d60765506300041ec38caa0c6000a2d82195418c00146b0232a83180021761f650c63000627b2ae
  | 5 => 0x80028de0576504500061bc0aeca08a000c1d7698d411400146f02b1a822800307dd963504500060ebb2c6a08a000a1f8258d4114001c2f02b1a822800385205635045000616bb4c4a08a000e0d63989411400185eecb1282280030b5d962504500070731ac4a08a000e0d635894114001c1d06b1282280038360d62504500071340ac4a08a000e2581589411400143b0d9928228003075db325045000706b1664a08a000a1d864c9411400183aec99282280038358932504500051ac36e2a08a000c3576dc5411400162d07b8a82280038558f715045000712b16e2a08a000c35769854114001c2ac730a82280038958a61504500061bbb2c2a08a000e16635854114001c2ac6b0a822800389989615045000712b12c2a08a000a37825854114001c2e64b0a8228003854c961504500041ec34e8208a000a3586507311400186aeca0e62280038558d41cc45000712b1283988a00083d869d2311400107f0eb2462280020f61d648c4500060f3a2c7188a000c1d7458e311400185ce8b1462280030b5d1628c4500061b3a2c3188a000c3574586311400107b0d3a062280020fe1d640c4500041ec3ac8188a001c3a70590311400183ce8b186228003075d1630c45000e2d382c6188a00086d869c8311400185ac939062280031358e720c45000616b22e4188a000c4d635c831140010df0eb1062280021b61d620c450006173a2c4188a000c2d7458831140038d4e0b1062280030d9d1610c4500061aba2c2188a000c667258431140018cae4b0862280071c9c1610c4500051ac3282188a000c35765043114001c2ac6a086228003495c9410c45000712b1282188a000c39645c031140018b2c6b8062280031a589700c45000638b0ae0188a000d31415c031140010bb0d39e42280030759273c84500060eb22e7908a00085f8758f21140010bb0eb1e4228003139cd62c845000626b9ac5908a000a4d864cb211400189aec99642280038359132c84500062b39ac3908a000c55735872114001c8a64b0e42280020f61a74884500041fc3ac9108a00083d87592211400183ce8b1c4228003075d16388450006173a2c5108a000c2d7458a211400186ce8b0c42280030d5d161884500051ac3283108a000c35765062114001c2ac6a0c422800389589418845000526c3264908a000c4d764c92114001c1ac89924228003914c961484500051ac3282908a000c35765052114001c2ac6a0a42280038958941484500078299282908a00083d869d0211400107f0eb2042280020f61d640845000e1d382c8108a00085d869cc211400183ac939842280030759173084500042fc3ac6108a00085d8758c211400183ce8b184228003075d1630845000e2d382c6108a000c2e74588211400185ae8b104228003139cd620845000626b9ac4108a001c6a705882
  | 6 => 0x51bc0ae8b08a00083d84dcd611400107b09b92c2280028da1376584500051ac26ecb08a000e167498d6114001c2ae931ac2280029560a63584500070b3a2c6b08a000e157458d61140014af04b1ac22800295a0e62584500052ac1cc4b08a000e26749896114001c4ae9312c22800391a0e625845000722c1cc4b08a000e26745896114001c4ae8b12c22800391a0d625845000722c1ac4b08a000a5786cc961140014ab0d992c2280038599332584500070ab2664b08a000e4662cc96114001c8ac5992c22800295e1932584500052ac3264b08a000e16644c96114001c2ac8992c22800391989325845000722b1264b08a000a56839d161140014ab073a2c22800385a0e74584500070ac1ce8b08a000c37875d1611400146d09b9ac2280028d61373584500061aba4e6b08a000a36841cd611400146b0839ac2280030d5d0735845000533410e6b08a000a65821cd61140034e50039ac2280021da1f43584500043ac3e86b08a000a668290d61140014cb0521ac2280028da1372584500051ac26e4b08a000c3574dc961140014ad07392c2280029560e72584500061aba2e4b08a000a36841c9611400146b08392c22800295a0c72584500052ac18e4b08a001a72801c961140014ad07212c2280029560e42584500043b43884b08a0008758710961140014ad06212c2280029560c425845000d3940084b08a000a7180109611400146d09992c2280028d61332584500070b42664b08a000e1584cc96114001c2ce9992c228003855d332584500070b3a264b08a000e15744c96114001c8f04992c228003919c9325845000722b9264b08a000e47424c96114001c8884992c2280021761a73d04500060eb24e7a08a00094d829cf411400183ac8b9e822800217e1d63d04500042ec3ac7a08a000c4e7358b411400189ae6b168228003159cd61d04500062ab9ac3a08a000a1d839db411400145b053b6822800307a0d76d04500060ec1aeda08a000c35815db411400143b0d39e8228003075da73d045000586c14e7a08a000c1d765cf411400183aed31e822800307dd963d04500060ebb2c7a08a000a1f8758f411400143b0eb1e822800287e0963d045000616bb4c5a08a000e0d6398b411400185eecb1682280030b5d962d04500070731ac5a08a000e0d6358b4114001c1d06b1682280038360d62d04500070739ac5a08a000e0d7358b411400123b0f99682280028761b32d04500060ebb665a08a000e0d62ccb411400143b0c9968228003075d932d045000706b1265a08a000c35769874114001c2ac730e82280038958a61d04500061abb2c3a08a000e16635874114001c2ac6b0e82280038998961d045000712b12c3a08a000e16735874114001c2ae6b0e822800385cc961d04500070a992c3a08a000a1d839d9411400145b053b2822
  | 7 => 0x2f815916214001c1cc939ac42800383592735885000707322e6b10a000e0d645cd621400149d07ba2c4280029360f745885000527418e8b10a000a4d831d162140014cd023a2c42800299604745885000d35400e8b10a000a2e849cd621400145b0939ac42800383a12735885000706c24e6b10a000c4f875cd621400189ce8b9ac428003131d173588500053340e86b10a000a6581d0d62140010dd0f21ac4280021b61e43588500052741ee2b10a000a4d83dc5621400189ae7b8ac4280028ba12715885000516c24e2b10a000c4d735c5621400145d0838ac4280028b610715885000527418e2b10a000a4d831c562140034d50038ac4280021761a73908500060eb24e7210a000c1d645ce42140010bf0eb1c84280021761d63908500062739ac5210a000c4d7358a4214003874e0b2084280021761a73108500060eb24e6210a000c1d645cc42140010bf0eb1884280021761d631085000e2d382c6210a000c4e73588421400189ae6b1084280071a9c162108500043ac34e2210a000c35649c442140018aac738884280031958a71108500061ab22e2210a000c55635c442140018cac4b8884280030e59170108500062cb1ae0210a000c69625c0421400107b0d3a664280024d60674cc8500041fc3ac9990a00083d87593321400183ce8b1e6428003075d163cc850006173a2c5990a000c2d7458b321400143b093b664280029560676cc8500060f422ed990a000c1d845db321400189b04bb664280028761a74cc8500060ebb4e9990a000b15819d3321400183aecba66428003075da64cc8500060fbb2c9990a000c1d76593321400143f0eb2664280028761d64cc8500050fc0ac9990a000c4d7698b3214001c1ac93166428003135d962cc85000707322c5990a000e0d6458b3214001c1ce8b166428003835d162cc8500050ec24ec990a000a55819d9321400149f04bb2642800313e09764c8500060ebb4c8990a000a4f82591321400183eecb226428003075d9644c85000707c12c8990a000e0c82591321400143f02b2264280029361b724c85000626bb6e4990a000b0e84dc93214001c1ac9b926428003135da624c85000706b24c4990a000c4f765893214001c1cc8b12642800383591624c85000527c0ac4990a000a4d86d09321400189aeda12642800383593424c85000526c3084990a000c4d761093214001c1ac82126428002d1604424c850005a4c0084990a00085d869cc321400183ce8b1cc228003075d16398450006173a2c5308a000c2d7458a6114001c2ce8b1cc228003855d163984500052bc12c7308a000e267458a6114001c4ae8b14c22800391a0d629845000722c1ac5308a000a5586cca6114001c2ac9994c2280039158b32984500052ac3265308a000e15644ca6114001c8ac4994c2280028d60674584500
  | 8 => 0x82b8063280020fe1176c865000626b9ac590ca000c4d764cb21940010bf06bb443280030d5d161886500061abb28310ca00083f845d921940010bf06bb24328003135d9324865000722992c290ca000c35765052194001c4ac4a0a4328003c14c9414865000f15282c8b10a000a2e849d5621400145b093aac4280069aa0054588500041ec34e9a90a00083d87993521400183ae931ea428003079d163d48500060eba2c7a90a000c2e7458b521400185ae8b16a4280030759273948500060eb22e7290a00085d8758e521400189ce6b14a428003135cd629485000e1d382c8290a00085d869cc521400183ac9398a4280030759173148500042fc3ac6290a000c4e73588521400189ae6b10a4280028d613529845000f29282c6b08a001e625058961140014ad073aac2280029560e755845000d39400a6b08a000a3684d49611400146b09a92c22800295a0e52584500052ac1ca4b08a000a568314961140014ab06292c2280069ca0052584500042ec34e7a88a000c1d649cf511400183cc8b9ea2280030759173d44500042ec3cc7a88a000c4d7398b511400189ce6b16a228003135cd62d44500062b39ac3a88a000c5573587511400107b0eb24a228003079d163944500060eba2c7288a000c2e7458a511400185ae8b14a2280030d9d161944500061aba2c3288a00083d869d0511400107f0eb20a228003079d163144500060eba2c6288a001c5a7058c511400185ce8b10a2280030b5d1621445000e35382c4288a000c3674584511400186ae8b08a2280021d60773590500042ec1ee2b20a000a3681dcd641400146b03b9ac8280028ba0a735905000516c14e6b20a000a1e839c9641400143b07392c82800287a0c72590500050ec18e4b20a000a36811c9641400146b02392c8280068ea0072590500050f41ee2b20a000a1d83dc5641400183d07b8ac8280030760f71590500050fc0ac9318a000c1d645ca63140010db05ba2c6280020f6137258c500050ec0cc8b18a000a1f81591631400183cc9b92c628003075937258c5000527416e8b18a000a4d82dd163140014ad033a2c628002956067458c500050f426e4b18a000a1d84dc9631400183d09b92c628003076137258c500050f424e2b18a000a1d849c5631400143d0838ac628002876107158c5000527410e2b18a000a4d821c563140034b50038ac6280021d61a71d0c500061ab24e3a18a000c55639c7431400186ac8b8e86280031558d71d0c5000436c34e5218a000c2d649ca431400189ac739486280030b5917290c5000626b1ae5218a000c1d649ce621400183ac8b9cc4280028be05649885000706b24e7310a000e0d645ce62140010bb07ba2c4280029360a735885000527c12e6b10a00085d83dc5621400149d07bb2c4280029360f765885000516c0cc8b10a000a
  | 9 => 0x65d05210050ec1ccba0a420083d87995414840143b0732a8290802c560f515052100782996a2a0a4200f05325454148401868ecaa28290803311d9325052100783aa264a0a4200f05544c9414840152d07bb282908028d61a75505210058ac1ceaa0a4200b25829d5414840146f0cbaa82908030d1d9755052100593c12eaa0a4200b1583995414840164b0532a8290802c9e0965505210045b43cc6a0a4200a3586d4d414840146f0ca9a82908038518d5350521005c2c18e4a0a4200ba1801c9414840126b0fa928290802e160e325052100783a9264a0a4200f05524c941484015490c9928290803c1d4d325052100782a9a64a0a4200e87864c94148401d090c9928290803a1dd93250521007423b264a0a4200f06854c94148401e0b0a9928290803c19d5325052100782baa64a0a4200f06654c94148401e0aca99282908020f61275d81210042ec1cebb024200e8532507604840185ac8b96a8108029360b5458c210061ab22e3a984200c55635c7530840107b093acc4108020f61e64d48210041ec3ac9a904200c1d7498f520840183ae8b1ea4108021760e75984210060f322e7a884200c1d645cf51084010bb0f31ea2108021761d63d44210051cc26a53004200a5983d46600840107b083aac0108021760c75580210051cc20eab004200a59831d560084014d305aa2c0108029c60753580210051cc26a4b004200a5983d45600840116b023a2c528002a3211624ca5000466c10e6b0ca000a9483585419400186ac8b8e87280031358d7290e500049ac08e8b14a00083d81dd1629400146b023a2c528003135cd6290a500049ac0ce9994a000c1d7458f329400162b033a66528003075d974cca500050fc22c5994a00083f845d932940010ef02bb2652800287e11764ca5000527c12ec994a000a57815d9329400149f04b2265280029361b724ca5000587426e4994a000a1f84589329400161908b12652800383e11624ca5000706422c4994a000a4f81589329400149b0da12652800383593424ca5000526c3084994a000b458110932940016930021265280025360873586500042ec16e6b0ca000a4d821cd61940010bd0f992c32800217a1d3258650004a6c14e7a0ca000c1d645cf419400161b0539e8328003075d973d06500041fc3ac5a0ca00091d87ccb4194001c1ac4996832800287e0d61d06500042fc1aeca0ca00086f825d9419400143f06bb283280028be0976506500051bc0aeca0ca000a378158d419400107f0eb1283280038358932506500051ac36e2a0ca000b1683dc5419400143f06b0a8328002c520d61506500070bc1ac2a0ca000e1483585419400146f04b0a832800385cc961506500070a992c2a0ca000c35765073194001c2ac6a0e63280030d5d1618c6500061abb28218ca000d25725043194001a62
  | 10 => 0xb006200e1953505600c401c66a2a0ac0188038c545415803100719aa282b006200e3154505600c401ca2a6a0ac018803a490d415803100748a1a82b006200e3285505600c401c630aa0ac0188038cdd54158031007183aa82b006200e9283505600c401d2306a0ac0188038cd4d41580310074929a82b006200e3153505600c401d22a6a0ac0188038454d415803100719a9282b006200e3152505600c401d2664a0ac018803a44c941580310052cc2e62b006200e9141cc5600c4015630918ac0188039454e31580310052cc2a62b006200e91414c5600c40147300322a990802876126598f210054ac0ce931e4200a1d8499563c840143b093aac790802956067558f210041ec26eda9e4200c55635c753c840107b09bb2a790803075d263d4b210060eba2c7a964200a1d8499732c840143b0932a6590802c3613524cb2100547424c69964200a4d86d4d32c840168b03a9a659080293e19534cb2100547426ec9964200a4d869d532c840161b093aa6590802d1606754cb2100527c32ea9964200b0d8499532c84015930032265908029361b544cb2100527c32a89964200e0c6455132c84010bf0cb9ea3908021761e63d4721004a6c3a65a8e420083d8799741c840113b0f31e83908021760c7558321006463a264b064200a1d83996648840151b0539cc9108028760e65592210050ec1ceab244200a2d829d564884010bb07bb6a9108030b59172d52210042ec1eecaa44200a598018d538840107f0cba6a5108020f61e64d4a210042ec3ccb994420089d87993328840183cc8b9ea3108030759173d46210050ec1ccba0c4200a1d83995418840162b07a8a8310802a5a0e64506210051ac36a8a0c4200b2582d51418840146f0caa28310802a5a0f76506210051ac34eaa0c4200b15839d5418840164b053aa83108028de1975506210058ac1ccaa0c4200ab18018d418840146b0da9a83108028de1953506210070a31aa6a0c420093587d49418840107b083aac110803251cd41582210060eba4e732a4200c1e745ce654840183ae8b9cca908030b9d172995210062b39ae332a420083d84dc965484010bb07b8aca908021760f76d512100436c16edaa2420085d83dd9544840107b09bb6a6908021d60776d4d210041ec26eca9a420085d87997324840143b0932e64908021761e654c9210050ec24ca9924200b0d84d493248401898eca9a6490802a3a13764c92100526c34ea9924200b0d849d5324840168b033aa649080293e19754c921006263b2ea9924200b47815d5324840161b0932a6490802d1606654c921005a3c0aca99242008ce87991324840149b0daa2649080293e19544c92100706322a89924200d45751c5324840170b0838a6490802f0600714c921004a6c3a65a8a420083d84dd951484010bb07bb2a2908020f61e
  | 11 => 0xc401c1ac8a9ac4188028b612755883100526c1ea8b106200a4d859cd620c40151b0939ac41880293e1d535883100527c22a6b106200a4f8154d620c40149900a9ac41880293616435883100526c2a86b10620083d84ddb520c40107f0cba6a4188020f61e64d48310041ec3ac9a906200c2d7498b520c40185ae8b16a418803135cd62d483100632b12e3a906200c4d7558b320c40191ae8b1664188033158971cc8310060f322e7a886200c1d645cf510c40189ae7316a218803135cd62d44310060ebb2a7a086200e0d5358b410c401c8aa6b14821880307dd953504310058bc0aa6a086200e0d53589410c40162b07a8a82188038958b515043100712b12a2a086200a3586d51410c40162b07aa282188028de1954504310058bc22a6a086200b158590d410c40170b0521a8218802c5615435043100713aa2c4a086200e2554589410c401c8aa6b128218803a190d625043100742a1ac4a086200a35869d5410c40162b073aa8218802c960a75504310051bc32eaa086200a95869cd410c40162b0b39a8218802e160a73504310054bc32e6a086200a3586d4d410c40162b0b29a82188028de1953504310058bc3aa6a086200b158754d410c40162f0ca9a821880385e1953504310068bbb2a6a086200e177654d410c40162f04a9a8218802c5201535043100782a9cc4a086200e1553589410c401c4ccab12821880389595625043100782a9ac4a086200e2685589410c401c4b0ab128218803899d5625043100712baac4a086200e8683589410c401d0ce6b128218803a15cd625043100713a9ac4a086200e8653589410c401c4aa6b128218803a154d625043100702a9ac4a08620093587d49410c40162b07a9282188038958b525043100712b12a4a08620099587cc9410c40162b0b9928218803a158b32504310058ac2a64a086200c4d7558b310c401a2aeaa0e6218803a158941cc4310068aba2a7188620085f865d5310c40189aeab126218803455d5414c43100742b12829886200e495358a600c401e22a6a0cc018803a858941980310051cc26a53006200a5983d46600c40107b083aac0188021b60875580310052c402a6b006200e1553505600c4014b70ca9ac0188038699153580310070cb22a6b006200e4953989600c401c92a6b12c018802ace1941580310071932a82b006200e3165505600c401e22a6a0ac018803a8989415803100750b1282b006200a39841d5600c4014d3043aac0188029660f54580310052c43aa6b006200a5b8454d600c4014b704a9ac01880296e0553580310052cc2c86b006200ac98290d600c4014b30aa1ac0188028e61352580310052cc1ea4b006200a7181d49600c4014b30b992c018802a6613325803100568c0e64b006200a59854c9600c4014b307a8ac0188038654f415803100728a9c82
  | 12 => 0x802a5a1b71cc9410064abb0e39928200d15751c732504017230038e64a08020f61a754c9410049ac0cea9928200937815d5325040162b03a9a64a0802c5e05534c9410068aa98e299282009b1801c5325040143b0d3aa64a0802c360a754c9410058ac0cea9928200b0f825d5325040162f02baa64a08024761e654c94100586c14ca9928200b1581995325040161f04b2a64a0802c5e05654c94100547436e49928200e0d6518932504017130031264a08028761b524c9410068aba8e29928200b91801c5325040143b0732ec2a08028b60a65d8541004c6c14e7b0a8200b1583997615040164b0532ec2a08026960a73d85410068b3ace7b0a8200d15759cf615040170b0539ec2a080345a1673d85410068ac2ce7b0a8200d16659cf6150401a2acb39ec2a080361a0a73d8541004cac14e7b0a8200d85829cf615040130b0539ec2a08024d61f53d85410068b39ea7b0a82009378754f6150401a2ce6a9ec2a0803459cf52d85410068b39aa5b0a820099787ccb615040132f0e996c2a080247e0973d45410068bc0ae7a8a820091d87ccb515040123b0e996a2a0802c5a0f61d45410068ab9ec3a8a820091d83dd9515040125b05bb2a2a08024de0576545410058b41ee2a8a820093687d85515040162d07b0aa2a08024760c705454100496c10e0a8a820091d839d7605040125b053aec0a08030b594725814100546c14e7320820083f865d3521040107b0f326a4208022761e64cc8410061bbb2a2a088200a3786551411040186eecaa282208020f61372597310041ec26eda966200a4d8299532cc40149f04b2a6598802c560f51507310051ac36a8a0e6200a35869d541cc40162b073aa8398802c960a75507310051bc32eaa0e6200b17835d541cc40126b0fa928398803a158b32507310041ec26e4b2c6200a1d839d5648c40145b053aac9188021b60b76d52310060eb22e7aa46200c35645c7538c40186ac9b8aa718802476137254e310042ec30e0a9c620091d841c1538c40129b04382a718802556047054e3100647322e521c620083d849d6628c40107b09bb6a5188020fe1974d4a310041ec3cc9a94620083d87593528c4010bb0f32e65188022761e64cca310060f322e7a8c6200c1d645cf518c40107b083aac1188020f61372595310042ec1eedaa2620086d82ddb544c4010bb07bb2a8988021761e65cc93100526c14ca9926200a4f82595324c40151d09b12649880315594714c931004e8c00e29926200a1d83997414c40143b0732a82988028d60665505310051bc0acaa0a620083d84dc9650c40151b0539cc8188030759173d50310048ec26e4a98620095581dc9530c40123b08382a618802536087054c31004aac08e0a98620083d849d6620c40145b093acc41880293e09535883100527c32a6b106200e0e6454d62
  | 13 => 0x586c14ca9968200c1f7659532d040161f04b2a65a0802a3a1b724cb41005c2c0ec49968200c8d7618932d0401c1aca31265a0802e1604624cb41005c4c00c49968200a1d86d4932d040123f0cb9ea3a080247e0973d47410048ec3cc7a8e8200b0d8298f51d040123b0eb1ea3a08024761f32d47410050ec3665a8e820091d874cb51d040161b0531aa3a08020f61b72547410050ec3664a8e820083d861c151d040123b06382a3a08024b6087054741004c6c14e7b06820091d831d560d040138b0539e832080217e09739954100616ba4e532a8200c4d739ca655040189ce6b94caa0803135cd72995410062741ae532a8200c4d835ca655040186ae8b8ccaa08028ba0b76551410058b41ee2aa2820091d831c1545040125b04382a8a08021b60b7654d410042ec1cebb128200c39545c062504010bb07bb2a4a08029a600625494100616ba8c4a128200aa9801894250401872cab8084a08021761e65cc94100526c14cb992820085d87995325040149b0532a64a080293e09654c94100586c16a89928200b0f825513250401c1aa831264a0802b2600624c94100706b28849928200b89801093250401a2ea939e82a08034555273d0541004e2c14e7a0a820085d839d760504010db053aec0a080247e0973995410068bc0ae732a8200d0d739ca6550401a1ce6b94caa0803435cd72995410068741ae532a8200d0d835ca6550401a4b02b94caa0803459cd71995410068ab9ae332a8200d26725c66550401a4ae4b8ccaa08024de097199541004cb41ee2b2a8200a2e82dd9655040123b07b8acaa0802c5a0f71595410068b41ee2b2a8200d1583dc5655040126b05b8acaa08024760c705954100496c10e0b2a8200935819d4635040126f02ba8c6a08024b60b76d4d410049ac0eeda9a8200937815db535040126f04b8ea6a08024d60670d4d4100496c16eca9a820093581dd9535040126f02bb2a6a0802c5a077354d410041ec36e4a9a8200d1763dc55350401a28c7b8aa6a08024d60b7154d410041ec30e0a9a820092d821c1535040126b02382a6a08024760e75d89410049ac0cebb128200937815d7625040132d07b8ac4a08030e595701894100654b12e0312820091d83ddb525040126b03bb6a4a08024de0576d49410061bc0aeda928200937815cf525040126b03386a4a08024760f76549410049ac0eeca928200937815d9525040126b03b9aa4a08028ba1b725494100616bb0c4a928200b2980189525040123b07b8aa4a08020f61870549410048ec18e0a928200935811c1525040126b033ae64a08024de0575cc9410058ac0ea79928200c1e7654f325040162f02a9e64a0802c560675cc9410060f3b2eb9928200b17815d7325040123b0f32e64a0802c360a65cc9410058ac0ccb9928200b1781597325040143b0da9664a0
  | 14 => 0xd645cf519440107b093b0a4a880313d8d7290d510049ac0ce9b12a200a35819d3625440126b033a664a8803075d363cc9510058ac0ce9992a200c1e765d3325440143b09b1664a88020f612764c951004b8c00e2992a200a1d849d9325440149b053b264a88029360b644c95100587426e4992a200a1d84d89325440168b0221264a8802d2600424c9510052b436e2992a200c55761c532544016a30038a64a880255e1d32d855100e1b882e8302a201c35105d060544010bf04b98c0a880715c41731815100e2d082e6302a201c55105cc605440189d06b90c0a88031360d721815100e33882e4302a201c6a105c860544038ca20b90c0a88021761f32181510060eba664302a200c4d72cc860544010bb0e990c0a8803075d1321815100626b9264302a200a1d839d5641440145b053aac8288020fe1974d48510041ec3cc9a90a20085d83dd952144010bb0f32e64288030799173d44510060eb22e7a88a20091d831c154d040125b04382a9a0803139957298f4100626b2ae531e8200d0f545ca63d0401a1aa8b94c7a0803139d57298f4100626baae531e8200c4e855ca63d040189b0ab94c7a080313d517298f4100626aa2e531e8200a4d8298f53d040183ae8b1ea7a08029360a6354f410060fba2c6a9e8200c8d639ca43d040183ae931ea5a08029360a63d4b410060eba2c7a968200a4d8298d52d040183ee8b1aa5a08020fe1d6590b410061cb2ae02168200c99635c042d0401952c4b8085a0803075db54ccb410060ebb2a99968200a4d8299532d040149f04b2a65a0802c360b544cb410060fbb2a89968200b0f8255132d040191aec21265a080383594424cb41005c4c0084996820085f865cf51d04010bb0f31ea3a08029360a63d474100526c14c6a8e820085d831d560d040123b06382cba08024b60870597410049ac08e0b2e8200d0e755ca63d0401a1aeab94c7a080343a157298f4100686c2ae531e8200d0e655ca63d0401a1acab94c7a0802a3a0b7658f4100586c14c7a9e8200c1d7658f53d040161b0531aa7a080307dd96354f410041ec36e4a9e820083d861c153d040125b04382a7a08024d6047054f410061ab2ae23168200c95635c462d040194ac4b88c5a08030e5957018b410064cb1ae03168200ca9625c062d040183aed31ea5a0802c360a63d4b410060ebb2c7a968200b0d8298d52d040183eecb1aa5a08024760f7154b410041ec30e0a96820091d831c152d040126b02382a5a0803075db53ccb410060ebb2a79968200c1e855db32d040183b0abb665a0803075da75ccb410060ebb2eb9968200c1d7699732d040183aecb2e65a08028761b52ccb410060ebb6a59968200c1d7654b32d040107b0d3aa65a08024d606754cb410050ec34ea9968200b0d829d532d040162b033aa65a0802c3e09754cb4100
  | 15 => 0xeaa08499002c3e19541093200586c32a82126400d0e76550424c801c1cecaa08499002c3e05541093200586402a82126400f05549c4424c801a1aa8b888499003519d57110932006a2baae22126400d86745c4424c801e0aa8b88849900351a157110932006a2c2ae22126400d46655c4424c801a8acab88849900361a117110932006c3322e22126400d85645c4424c801a8ea8b888499003619517110932006a2aa2e22126400d85545c4424c801a0aa8b888499003c25527010932006e0b8ce02126400d0d545c0424c801994ecb808499003529d57010932006a4baae02126400d8a745c0424c801e12a8b808499003709c57010932006e0b8ae02126400d4b855c0424c801a910ab808499003529957010932006a4b2ae02126400d8a645c0424c801b12c8b80849900352d517010932006c52a2e02126400d49545c0424c801b12a8b8084990034255170109320048ec24ebb0a6400c59655c0614c8019a2c2b80c2990024761275d8132004aac0cebb026400c55651c5604c80183ae931ea41900313dd9524c83200547424c69906400a4f8654d320c80189eeca9a641900287a127558f510050ec24eab1ea200c1d7498f52d440183ce8b1ea5a8803075d163d4b51006173a2c5a96a200a4d8298d52d44010bb0d398a5a880217e1d6314b5100526c16c931ea20086d82dd163d440107b09b92c7a880293a0b6458f5100526c16c8b1ea20085e8719163d440149d05ba2c7a88029360b7458f510052ac0ce8b1ea200a1e84dc963d440143b09b92c7a880307a137258f510060ec26e4b1ea200a1e841c163d440143b08382c7a880293a087058f5100526c10e0b1ea200a55811c163d44018aac738e87a88031558d71d0f5100626b1ce521ea200c4d635ca43d440183ae931ec5a8803079d163d8b510060eba2c7b16a200c56635c762d44010bb07ba2c5a88029360a7358b5100527c12e6b16a20085f8758c62d44010bb073b685a88021760e7690b510042ec34e7216a20085f8758e42d44010bb0eb1c85a88021760e7610b510042ec34e6216a20085f8758c42d44010bb0eb1885a88031558e7110b510061ab22e2216a200c55635c442d44018cac4b8885a88031658e7010b510061cb22e0216a200c59635c042d44018d2c4b8085a88024d60674ccb510060f3a2c7996a200c1d7458f32d440183aed3a665a8802c560674ccb510060ebb2e9996a200a1d849d932d440149f04bb265a880313e09764cb5100527c12c8996a200b0e84dc932d440189aeda1265a8803135d8424cb5100706b2084996a200b458110932d44016930021265a88020fe11729835100626b9265306a20085d8798c60d440183ae9318c1a8803079d163183510060eba2c6306a200c4d639c860d440189cc6b90c1a88031358d72183510060f322e7a8ca200c1
  | 16 => 0x2595320043ac0eedaa2640087581dd9544c8014ad03bb2a699002c3a137254d320048ec20e0a9a6400955811c1534c80107b09bb2a4990025361f53d093200587c1aa8212640094d87d4c424c80161b09a98849900253e1d531093200586c2e862126400b8581d0c424c80161b0aa188499003495517110932006a3a9ae22126400d45535c4424c801b0e86b8884990036150d711093200694aa2e02126400d4b535c0424c801a92a6b80849900362d0d7010932006c4a1ae021264009a5819d3324c801a1ce9a9e6499003439d153cc9320041ec24ebb0a6400c59535c0614c80107b093aec0990021d60675d813200687c12e932a640091f815d2654c801a1ce8b94ca99003435d17299532004a7c0ae532a6400d15749c6654c801a8ae538cca99003459d171995320068aba2e332a6400d45725c6654c801a2d08b8cca99003456117199532006a2c12e332a640098e84dc9654c8014ad03bb2ca9900247613725953200587426e4b2a6400d0e84dc9654c801a1b09b92ca990025360772595320048ec20e0b2a6400955811c1654c80129b053a8c89900253e097519132004a6c16edaa2640095581ddb544c80129f04bb6a89900253e0572d5132004a6c14e1aa2640094d82dd9544c8012ab03bb2a89900253e09765513200587416e8aa26400d0f64dc9544c801a18c9b92a8990025360772551320042ec36e2aa2640085d861c1544c80129b04382a8990025560470551320050ec24cbb126400a5581997624c80132b033a6c499002c361265d8932005a2c0ccbb1264009c5819d3624c801a1ceb3a6c499003435d674d8932005c2c0ce9b126400d0e859d3624c801a1b0b3a6c4990034399674d893200686b2ce9b126400d86819d3624c80131b033a6c4990036160674d8932004c2c0ce9b12640094d87d53624c801a1ce9aa6c49900253e1d54d8932006873a2a9b126400d0f825d3524c80123f02ba6a499002c3a1362d493200686ba6c5a92640091d84dd9524c80129f04bb2a499002c3a137254932004a743ec4a926400b0e84d89524c80123b08382a49900255604705493200586c26a5a12640094d87997424c80161b0932e8499002d160665d0932004a7c3acba126400b0f84597424c80183cecaa48499002476127550932004a6c14eaa12640094f825d5424c80183cecaa08499002c3e09541093200586c26a42126400b0d85508424c801a2aa8b88849900351d497110932006a2a92e22126400d85425c4424c801a32a8b80849900352d497010932006a4a92e02126400d89425c0424c80129b0f3288499002c36126510932005a2c0cca212640094f87594424c80161b0b3a08499002c36166410932005c2c0cc8212640098f87590424c80129b0faa08499002c36165410932004a7c3aa82126400b0f87550424c801a1f0
  | 17 => 0xa48400a1d849d563908014ab033aac7210029360b5458e4200527c12a8b1c840087581ddb539080183ae8b1ea7210032598d71d0e420060eba4c7a948400c1d7458f52908010bb073acc3210021760c755824200616ba2e532a840085d83dc565508010bb07b8aca210024760f715504200496c16e2aa0840091d831c1541080125b04382a8210024d60470550420060eba2c7a988400c1d7498f521080183ae8b1ea4210034355173908420041fc32eaa10840085d839d661108014ab073acc2210028d61352984420051bc0aa8b088400a37865516110801c2aa931ac2210038555163584420052ac1ceab088400a35859d1611080152b073a2c2210028de1d54584420051bc1aa8b088400a3782551611080146900aa2c2210028d61353584420051ac2e86b088400a358550d611080146b09a92c2210028d61742584420051ac2a84b088400e3154586601080147309a94c0210021760c75580420043ac08eab008400a388055160108014770caa2c0210038655263580420070caa2c6b008400e31549856010801c62a8b0ac0210029660c755804200538c08eab008400a3887551601080147706aa2c0210028ee0954580420051dc0aa8b008400a3984d4d60108014730ba1ac021002ac60743580420051cc2a86b008400a3984d4960108014730ba12c0210038a552425804200564c1c84b008400a3985509601080186ccab8cc9990030d59571993320061b3aae33266400c35755c664cc80192ce6b8cc9990030da1571993320061ac2ae33266400a358199354cc80183ac8b9ea9990028d60664553320060eb26e6aa66400a358199353cc80162b03326a7990028d6066454f320058ac0cc8a9e640091d841c153cc8012ab02382a7990032559271d0f320041fc32e9a96640083d8799352cc80146b03326a5990028d6066454b320041ec20eab06640091d841c165cc80129b04382cb990025560470597320068b3aae33266400d15755c664cc801a2d0ab8cc9990034561571993320068b32ae33266400d15655c664cc80152d03bb2c999002c560664d53320060ebb2c9aa66400b158199154cc80183eecb22a9990021761b71553320042ec30e0aa6640094d821c154cc8012ab02382a99900247e1974d4b320048fc0ae9a96640091d8799352cc80162b03326a5990024761d64d4b320058ac0cc8a96640085d86dc552cc8010bb0c382a599002476107054b32004aac08e0a966400d15545c442cc801a32a8b8085990031659570187320064cb22e030e6400cd1615c061cc80132b033a6c19900247610755833200692aa2e22146400d29545c0428c80134b033a665190020fe05749953200626b9ae532a6400c35749c6654c8018aae738cca990030d9d171995320061aba2e332a6400c36845c6654c80186b08b8cca990020f6137
  | 18 => 0x803400600000600000e00200201200401003200000004a00a00e00400000200200c00a00001000800000000401401400400a0085d83dc562d50010bf06b8cc1aa0028d607545865400466c14e7b0aa80094d829cf615500145d05ba6c2aa0028d60774d855400526c14e7b0aa800c1f845cf615500183908b9ec2aa00217e0973d85540042fc12e6302a801c1f405cc605500383a80b98c0aa0030be11721815400616422e4302a800c4e835c8605500189b06b90c0aa0070bd01721815400e35202e4302a801c2d405c8605500186d08b88c0aa0030d611711815400e1ba02e2302a801c35405c4605500107b09b92c3a98020fe1172983530045ac0ce9b12a600c37645c66454c0126b033a6c4a98028d60674d89530060fc1ae9b12a600c1c835d36254c0107f02ba6c4a98029360b73d89530052b40ee7b12a60083f815d06054c0383e60ba0c0a9807074c174181530062741ae4302a600c4d835c86054c0389e60b90c0a9807134c172181530061b422e2302a600c35845c46054c018af06b88c0a98031520d711815300e2b982e2302a601c72305c46054c038aa60b88c0a98029560e75987430052ac1ceab0e8600a3584d4d61d0c0146f08a9ac3a18021d604755834300516c24eb3148600aa581d0e6290c0145b093aac5218029360f5458a4300527c1aa8b148600ac681d0d6290c010db043aac121803075d173995430060fbb2a6a188600c1f765514310c0143d073aac9a90028760e75593520043ac0ee6b26a40085d83dc564d480146d03b9ac9a90028d607735935200516c14e6b26a400a1e83dc564d480143b07b8ac9a900307a0f71593520060ec1ee2b26a400a1e831c164d480143b06382c9a90028b60870593520051b408e0b26a400a35811c164d480107f0eb20c9a90030d59271d8f520061b322e3b1ea400c35645c763d480107f0eb20c7a90030d59271d0f520061ab22e3a1ea400c2d649ca43d480185ac8b9487a90030759273d87520060f322e7b0ea400c1d645cf61d480146b033a2c3a90028de0574587520041ec26e6b0ea40083f8759061d48010bf06b8cc1a90020f61e64183520060eb24e6306a400c1e645cc60d480183ac8b98c1a90030d59271183520061b322e2306a400c35645c460d480183ae931ea529003075d163d4a520041fc3ac8322a400c37645c7435480149b0539ec2a90020fe05741815200e17902e8302a401c3a205d0605480385a40ba0c0a900713c81731815200e26902e6302a400c36845c4605480186b08b88c0a900719c81711815200e39102e2302a401c65205c4605480143b093aac629002956067558c520060eba4c7a90a400c1d7458f52148010bb07b8acba10021760f71596420048ec1ee2aa4840083d861c1549080123b06382a9210024b60870552420049ac08e0a
  | 19 => 0x400201201403800600001c00000200000401a00000203400401800400402800200600000000000a00000e01c11600200000400a01800a0000020000040020a800204c00201200207c0020060000240000fa00200a00600000001600200001c00200000400000000600a01e00800c00000800000000a0020000020060020020020fc00001000000000802200200200e00800408800200c00e00800000800000201605e00200000000000e01000000200400203a00000400e01c01600001002c00000000801e00200200400000801200000800201601600200601001401a00402a00800801001600e00400002800603800002400000601400201a03402001200a00800a00601400200a02800000000000200c00c00200200200000400c00201a0000000b000200601000002602003c02401200600402000000004000a02201e00e00200400000000000000800000002400c01200000000001201c00000000000200007c01c00e00001c00600000000200200c00001000800401400000a00000c00000000800c00200000200600200202e00403000600200201001800800000213400000001202e00000e00400a01000000000000800000001c08606400400000601c00201a00a00e00c00600602800000006402e02c00000000e00200200200800600000200600200c01000600400200c00200403600600000000201e03400400600800000401000001600200203200402a02601800400400000c04a00600c00e00001400401404800202a00400200e00401205200003000e00200601800200200a00201000000800200000200000600002200600200a00600400000601200000c00001200e00000400801802400000000000c00800002600a03200000200e00000201a02400600000001c00600000601001000600000202400400800000001200000000201a00800602402200200600000000a00000400800e00000000a01a02400201406c00400400801000203400200800200000200000200201000000a00600400200400c0040020040100cc00200000000600000e00403200400a00602000000400000c01400400200e00200001c00601203000600000800000e01401600c01e00202402a00c06802c00200800a00a00603200000001a00000a00000c02000804200001200e02800001a00e00c02202c00200000006600a00200400002400000e01a01e01400000400000600000c00000000000200400601e00200200800a00200000000a00600a00000400000001801400000000000800000000000200603200400401000600001e00600400000003000c00001e00000200000e00001200800800000006800000c00800801c03a00000200600000600000000001c00000c00800000000200401c00200002c00001400000000000000a00200200c
  | 20 => 0x65803a0928e08540101117c000000289a6893be7094b38818eae000300011825239a0000c20ca829a30396d129600025e0ee4b3a0002eca2bd3de74a33705ec00003d0a5800000000000000002a697e3b2969800000022300005ea0bf018000058e3cf4a015bc0007bf0001bd40000ca35b0000aa09cf4700bd8fbe05a2768c9447a8b34d09acc00682112c0478c0c3d73bc97941661fb250000000046a02b9a000005e8000000000083a33c9aa80005c8000000025c0000000000fac53a0002548abe5c710f8e946800000d980013860004a81938c8c0001b10000000000000023ce6679229611e00a49321e900005629563338da0000a2832982b8f760000b390b8be0000101802c00018343917f4ed63614000bc109a56d43294ec5d66ce2d203c052c43933296712f42971f9910c60879845f09dcaa69391ca06ac5aaa38374831c06c0000001bf400054d0791b400880341b790400d04f300012189180000001fd83e800016111281241631471e4cff06173bb1c580000000000000764a29000000000000000002b45a200029500011429de2bb800000000039f909c67e9ed0de124114c61c00000000000000000388fd07fd2b280000007142b104f14483e52f7a400d625870001fec6ce7f000015f05f40004758ba82c097215597dc00058e44900000000000000000e9223c0101a6cfea11930c22a04088de2de1b1c0341284c59d700000e62bd13d494e287000000105000009c840409e532000000035056a0001e689ce5be00009a45322d0004837c93813702f94fc8482561a712009d453e15e83f091c0f70b28ed0d685042c481dd00600032785b13a45b2346114917483b3ea00dc1020871f5117099a00027c800098e586274995900c22136896cc2303521b30c40eb288d3d328c88902675100e6403c6440001c140009b12a41a2c00013a000171543a02e0000dac0007a84190000a222ba458a2e13cc9d308b03345a404a2c280010483b1179135c0003ad00024a942849934700000ea20c0000000fbc2e4000290000076a4d980013f474600000000000002d080003da6bf000000126200000000003fa4180ec08ec01202000a04a00002c00801e03e00000400400000400000803600000000601c00600e03c00e04a00201800600000400000a00801000000e00200200004c01401800205200200e00400c00000400005a02400000801200a00200800000003000200000200007600200204000a00400000800601200c00000a00001400401800400a00200c00401000000000000e03800001802600400000400000400000800605200200800c00c00800000407e00800402c00000200200c00001200200a03c00000001200600a00200001600600600000808e00004800e00000c00000000400000000800200600401400801a00a0000
  | 21 => 0x800089e96f09811c88c24f722992290be63b14a8e10c7ea2b21a85bc31480134c950822e93a36d98f834e75e2a31fb8a6a07611c1024be668f3a001840000000002324f841542e01ce8c6a0511e58ccd2980000f2199128a0000031fa494288e000123c000000000003475235a36002987ce0000a7963c710a183c380000000000001bc4f103ae13a9cd000000042d000000085923f8000b166c323a06493ac000255063862a62b38d0d3d13a405000000107e0001648001328091000061c0006a73fd1310b620003ba000000008b0001e5000049a3068000cee000000188c4688b94e314dcd300000002040000000442800000016602425b0000a07000276800000006b000114a72000000010364970000c08b062164260c140000002f500000000000000ead34a78c51a1eb85641cc3ee8768ee272906019a832c84e06788dc02a39822b970c2340324bd92b4cfc2c82da849474405b2310b383401ef4b007a041696e4200f8cb4a0ac24681f02b28b4001178813c976513052093a11f000000000000000000014781cd415800000089105f02100002463511e391b02b42968f3850c0003009ac80000000000a7c0005a0000221ce0c9150f4863d2609cb00012a0e260243910f40d46000012948d19a0004aa26645f60001a5098538a4e50c482c404e97d01c958535038503280000008ad1091b9cdc28792059e9463851212d955002e59b465000000000016e04b00006200000a9542c0800000000fd49b73e3851c1d055609c1e64a667f43a200001f4000214240888a4dc13a0000000000295a640ffe0000000c0c0000003ec00010fe7a233322243b80000000fd00ac4670001a70000000000000000086828600001a800012612102a25d246000011b806614f11049d893d275a68d42e2af2490cc12d08e109f84a8ed045e18e94d83c20002c114c08f84b204b13c90347a447d01c8f5a0003de21cc0006e203ca5e41d886011890e000097834a00000009e81460b840004193c0934d34c03c4cd26080e61c90000000d200001de9f8400065c17c80000009db13000009841b100023cc5a63e42d68c613d20002ca05d400000050c8a6c00000008509700000004259f140004cf0000cf02d240600027b85881f000005100002ae2fc265c00054c4b98000106689264000013000051b9d9873ea3f0999664b4631b1e519c400000000000003ce1153530000e0279e00021e00007770110e491786df33908b87380003e81dbc8800000000000ef800023980007848a90000acd39c42b1661224c206862d403a84e01d24a99d1c75088b0bb80002f200041386e51186e32e21df88984ce36a8cd4e30a0934898c000093e0661af8b2c77031999eca4055a49b0dc05283864869c6c6a69911bf260cf9800010794bd46659145ba54400058813c8705188
  | 22 => 0x2238000e3c0b200027407ee38b00021b000089b3548000000149000000132a00012599bc506a3d4641f2c00069731e100916009f38c800000000000004840004b70938c8c00044b0001ff01322c11220dec0003db00000008fa85b2ee142000061648200004320004f212c00f07f74920900992638166a7cc00026b00009383700000002578b8c9203c01f100d86f91c80804d7450d0df85e0ce610c16300002e64502b4229140c3772e4907000000000000000002f7000214c7f8796000136145c0000f89ec89369b033e8000cb28fb44997400000041080fc8000538204000000050f3ee000000000038e97f87b04661849c7c00056722d9ca90bc8b640598389309ca000082910c9f509a0e1c0000000001d2142490b000278400015e038891c00004314e0bfc57e66b3641b511e8000000173867c0fe2d58d7c8463c44e396b8bdc0000000c040000003f280010cc0001d8240c482000000055c0006451a225181ce00014795b800051a241821480013148f8a103b600000015742b60dc00000000000004f58c38b5e4c519080000001843798f5400052833022b000000000506a40003f81be184400049641980000001c5000000056a8903129d080004da46ca76461e2df4881aecc2450616198b52380000000bb8b0800021d91c08881ec4f91b14a208521b1886c0245cf10ea5603f000049428700007ef2ba800096240d1248934000426234a09426447a1ba80ad00e00048a00006b200031e88b0ca22cb5068a98a4430c19000b030a5720000e906a03c630d01247707b506996dc02208c24a1f00a2e0013cd9454a165f509b079468c6ca2009e2940a92e00000013368473178f992b676027d94d036e26847f23412cc0001950000ec415d0001ce528e35c3ce266000025a1fe8820ae252615401f4a629bb5169abc61a0004790001236000088000000001000021180005d1000000124c0000000f1c00011d000245c0007e03a180005bc2110000fe8ac63a103f000000033a2829f340008cc20b000000000027e12b8c44000501983cc4283543a06c00009ea2a89c9400059f409a42124675d000000000048b0000000dd604000000000000000d7951cae68f10a60d78000000000000038e2d41679fc800000007a1a582065e435b81a40000003ec8894a320d903101c0248000451275000027800015790b86c6000000068232d232194800019b0000a4cfd80002b5a6b530a00000027544ca0003af843ccae43e50f247902c61900000fc00080e00000000002091c6800074626600000010784af2ac8001154000000128d302000128a6a8dae70844d176c1c803e3210ff92428e34219bb80000000e500740000c1000000075817644a00000008671298a14f728110000d1525e0000000db40000001228000a9c0000000000a3c0003cb
  | 23 => 0xb1490fb61001e60a210402324fb80010543c50fc82a14209d72ec090845a1cf4348fb8b980001c5000000033d01080000dc4e40001b300000420ae1bdcafa5073760bb0c5c00043ba6bc00000038725ad4867860ef110946000046182d85ae46d0649a480004330001cb00006a40149f042240003d516fc00062c2ef21f4e7850e4e202a907204547c0dc53100001bc1d68ca03eb35706040005f617c0e80dec6853a5808c8ba0000b52588e1e783374164800048500000b4fe623f0000000c5060813903080000002530cb000061b0000020000364000231940014331a00001265a74b2874c02ca36491085c0004f82318000f660bc0d0812c80697f000000125806f12f8f8000000012900000002594ff0b749b628d238949cd429f600016b00001ae424175864c94a00024fd1307b03e48000ac84a92f186b4000a21511a1bc93c5b821500000007281bca5c40000003c580007fe00000022b903235d494807c0003d40a71c9000002f000000000069e000178400000000000007bc9a7000000148400046d9cb4aa405300000005cc0001ca8a4843870d4a4095c7368d4000000000000000017a495600044505893b000033b029c0001ac00023080002f40c58000702000193a41c21c0002f596ec3387733e328540009354ce800058010451c806136453c1400f7c81c1bb388218865c8511f41f54d3ea460000280e3844e0000ab4a3e00017887650605cb49e05053e24ff0e58d080000004c698080008e80c60000ad8789341a63921e03306c00014180004aea5240005ba46ba20c2280003ab00005420470000974dda00000000008b079d2aa800000053d47f8c5c8148d126608a928689707a80704da7b63d0a3bc17a1ff32525a40f62aa0e8a1ec1b68494c389b889a91341a000076c15a3130000b3402a18f82910f428b1b51bf83264e60000bbcd100a13382670e184d037012040b80ff0189eac00023034d27f03a000005c2270baa014000097926e0000e303441c00ba17ea0a4f860000a505f0ef69ac224a6e8fa24ca37825650180000001af400060b00013c4c2a0003f2000000032211c8000cf800000019d490e0004aa9978e4e6c100018311ec1df35027c094a65d000000121c00000000000000001be95f800000000003203ae0c300025a83807260001ae400000000000000009383cf977d2843ec377a83d30840f00028d4ff24e000000000005ff2bc06d898217144100000007c81c7a49455800033a18e43483394c9a7880001e022d1c00fb419f1fb02a400041f5070a8c0007030918f754884f424990892664591920000c1227d28ea08800098623b89ecf7000011d0208a880002ee9d8d2120004c9280903032b0ca00007187e2000284c99695a009800046642c0000000dcc8ea1e680009e06e44a082691ee1f6000000000
  | 24 => 0xa7670002390c9a9be02c140010c54b0001f9800095751602740000e115e1bec0000000b58988ed219800012e80002a90001b74ea25b60e180006f48e242092542aa0002689ac04aa00015b83407743b5000086800037400000000004314ff800024041525a0000f2a8bd44220d847c8a343b03393122e951d035466c1fa072a2fcb204fd0a31144c8264c3bd000000000032d10c8ee462a13190454824e11712700bf42b9000235862c0d74b69404bda7361b9a89ceb663146a9f3cb94000346800000036e4b191b8000000000187c0000002358f8930051c21a05fc04c1c2495a6812b805e2b4a2780768ed1c49db800035b41890fc61486d0001e1077800007b26310ac00000007983c64130000000000681000000016873246583cd16a1063248a04f525d34a726d13c076141e9d54acc03831912e136c91a4fa041cc1400026180010c61f34780dd80001be3a910780000894fc00380003834af873884234b00000000007bd52280000005250001f4cd9a6b530e8c2ccc60000d915d8f680002f3223cffc8500000000bae9cd1d3049800000000000009a48bb00017680009fd04400000000004699ce000000034e80004f46134c505b40000003971fc4904a225040000a365a21c887d40004be36f1ae0000332000231c0004f627403f543e2ca2169b4883a6d632f90804ec00011b11b0a8a0d20ea9984000805444179c000000356813929e15250087b825600002a03140001990000a447ea1680001db116400019426d41f007f0a1000000028a00000000000004e89030d4a96147e871105e41b4671a280006f20afa1f00005bd47280010e20000001c5c000000000026c2e48ab002893c000518364a4ec00029d16296e4e429c100387f0000782323885000000000000013c668736c00000000001a40ba07665933b227710104653c28ea89f482c00003107de9a43a79f9c00097015c000087a5f4006000106e51451f1f380000002cc09bc98036c44b20284f881e0c30a0872600017f000060e1bd00000008340005129628ae081f1149edcdd470b0da246123a3000000dc80000000969634c4e0af406800020458c26e8d6137838e4358e7863c0003ba8a4040e17e10280000000000001364000314483105ce2426a24fa1f84560000dd115094854a0000d24db420e0d1828c74e00051780000005210e400005ca0004a200000009fb2cb8000e560000000000f220004cf0154b9a11c086a1d50c23c93d38000576a044770edc5e613d4df860800000027f000096657f1a19428dfe00012421c0da615602c8bb448608a04b9890d9e2a011382945b22e70d311a019643c4c7a0086705c1000000012831349a153c2c2927000220417266221d1aa103a4a24bb81b43224df36e0d1c5f813e00000000005b033f88a04fc754000000000000015
  | 25 => 0xcb620d03180008aa0000ba1cd4e625953df0a2477e78d3d012f4fda84526aa6acbe492d0c803b886e655341067865e74d2ab8f707f21500759cbc9ac84204e00000000005050000000357453a11118a684000000000000000019e07a20bb000000000025005824487b20280eb1aac440629482a254f5855800023e400085410f000000008e00000004c882e2bc92b02e081c00003a5434060000000042a69500000013d800016c000000054107d800000080f3a6286c3ee55b1f80f68000000000000043000032000d522c6051aa800096c000432160409a13508410c028a2e02149b2cb5447b248819cc2882615f01910121e205a9ab05c65f106f0cdc7c239d2778f582f466c3621de0fd66481fd86880001dd0c00d3400019a00000000002da4dc87a8000460000180c0a000000021b8f1e2710d50000000693048065cc3c00016b1ec4000a1111225d107c90a000084c0003d31cb80005b6000000239800012f1b29010e0400033d24448fc711153a1a90ba63a4401580fc69c804a8f0060c8dd0000c682760000000c44a060b7000000139885748ca0b48288e9084990d0085743bea13c96a42f4760cec0365fb05101e82fa34c46d00652180f106d0c649bc4253340d588ea6fa2f611bc34a5291521b0902822315825902161eb2a499a43fc58039f0ca4cda16e0559cf4f74488271a39cefe3be0caa2809a855c4be07502c85160351be06a29a908d8da50701580c423f046a8154251af0fae08d46f9f286628124e110d8e828231f8950c7900dd40b98109766fc4cb1048e9c8cf4cf97e53ca3340079f480829bd398140880e6d927705351822540f909fc1de3604809b94b8489922b0e594769dd2ea1cdc18c52e3b6800075e1b510003b40003823ac25d422626c07ca79c78294d4dc12fc53050923b1c28b3ca0b0000fa51a47901c016a445e73b0260f0c4e664b071a160ea65390ce92e4bc057b1890500e2a1222631bd00ba18d03584449c49ae1aa27e54627a311127254547503d798dce0e3bb31b089913e8f500017f054447901d0dfce467451f6a1542
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1a0554604624c940006215d9811093210001a0565604424c84000682595801093210001681901093258440004a164484589328c00141597d95410c63000701d9572504318c001c1365505700c63000485a5b8154d414c001a055360861505300062161972504310c001c05655c9410c43000704595415c0310c001c8162505700c430004a16468498d32c800128591a13764cb20005816446455132c80014159319571191200052164a735c4644800141593a1571191200050964a855c464480010359121974d49200045265c8054b32480013099420152cc920004d06448054b324800120c96613524c9200058164464d49324800160591191524c9200058164464d4d324800160591191534c920004a164684dd9324800120c96612754c920004c2650805d5324800134191201754c92000681d95811913248001a0465604644c92000483662751913248001605919d4644c9200062161d811913248001a0685604644c92000681615811913248001a0695604644c92000681655811913248001a0675604644c920006815d581191324800188987600644c92000682615801913248001a8181600644c9200058164464d51324800160591191544c92000505644645cf51480014259119172d45200060361c644cb51480016059119132d452000581644644c9514800160591191329412000505644645cc50480014259119172141200050365c644c8504800180d87191321412000581644644c8504800103598191711412000701191325c45048001c08765513250120004a164a8399141c400128592a0f7650710005816486354d41c400140d941957218d1000521646745c8634400140d94a157218d1000511646855c8634400180d7460863d491000511648635c7524400104d9221973d45100044c65c8054741440013119320151d0510004c86488054741440012149660f51505100058164863d4541440016059218d515051000681d518218d4144001a05546086350510004a164a83dd941440012149660e7550510004c464c805d5414400132192201755051000681d958218d4144001a04656086350510004856627518d4144001605929d463505100062161d8218d4144001a06856086350510006816158218d4144001a06956086350510006816558218d4144001a06756086350510006815d58218d4144001891876006350510006846158018d4144001a818260063505100058164863d4d41440016059218d53505100060561c63d4941440016059218f5250510005816486354941440012849858932505100052125d624c941440016059218d4194110006035d18218c504400104d9818d721411000511648635c450440014159718d41141100060561c6350450440016059218d41141100070118d725045044001c107654d414c110
  | 1 => 0x10058864a85505600c401621921d541580310058465683505600c40168192a0d415803100584e6153505600c4016119854d41580310058425d53505600c4016139254d41580310048c66352505600c40161193d494158031004a466332505600c40161195cc941580310058465532505600c401a1185507315803100684611538c5600c401a11855053158031005826406455132c84016119018d5350621006505d5801c53248401c0476551325052100681219534c9414840148697e193250521004a1a63764c9414840150597a1532505210058165a854c9414840160796615325052100681219854c94148401305989d532505210058165a754c94148401607965d53250521007011d9754c941484013059899532505210054165e654c9414840128591211624ca50004a164883585419400130591a13724ca50004c164484589329400160591211624ca50004c164a83dc541940013059220d615065000581648835854194001c05764c941486500048364a83dc5641400140d92a0f71590500048564684dc9631400141591a137258c5000489646849cd621400160591a12735885000503a53875cd6214001445911d173588500040d647875933214001415919d163cc850005096467458b321400141591a1176cc85000603a11825db32140018157660674cc8500048564787593321400101d97e0564cc850005816467458b321400140e94e09764c8500058164482591321400120d96a13724c850006035da84dc9321400130591a13724c85000483e6164dc9321400184576604424c8500068159181109321400184976600424c8500068259180109321400124592a0e74584500058164a839d1611400141693e1d7458450006095d1821cd611400103597a1332584500050565e84cc96114001215989d3325845000581a53824c96114001c05745c932584500051165c424c9611400164190109325845000603591829cf411400104d92e1d63d0450004136627358b4114001445929cd61d04500050364a835db41140018168360576d0450006035d9829cf411400120d92e1d63d04500040765f8258f411400140d97a0d62d0450004836627358b411400101d985db32d04500060361d62ccb4114001605929cd61d04500050565f32587411400141693e057650450005816488158d4114001a058360562504500048565a83dc5411400181576a0f7150450004c164a83dc541140012179858f715045000681a0d62dc54114001825865c9410c4500070158d72504311400142597589410c4500050c659415c03114001c1163505700c45000708589415c03114001605964c9414845000681619325052114001c05764c9414845000483663651093290001a0765604424ca4000682d958010932900012859220d615064000483a5b825513250
  | 2 => 0xc80150996551701093200542e45545c0424c80121591a137258f510050564684dc963d4401415919d163ccb51006055d9819d332d440140e94e09764cb51004c164684dc932d440184576604424cb51006815918110932d440184976600424cb51006825918010932d440130591a13724c951006145d9801c5325440140d94a157298f4100511646855ca63d040180d7460a63d4b41006225d98010932d0401a0965600424cb410041364b865cf51d040140d96a157298f4100541646855ca63d040180d7660a63d4b41006215d98118932d0401a0565604624cb41006225d98018932d0401a0965600624cb410044364b865cf51d040101d96e0973d4741004c164a83dc5545040182975600625094100682551801893250401a0965600424c94100641d51829cf41504019055460a73d05410064160d815ca655040118592a0f7159541004c164a83dc5655040150592a0f715954100505a4f815db5250401829766006254941006245d9801c732504019117560071cc9410064454d801c53250401a0965600624c941006445d5801c532504019067560a73d8541006415d5829cf61504015059299673d854100641a15829cf61504019058560a73d854100641a55829cf61504019059560a73d854100641995829cf61504019056560a73d85410054164a73d4f6150401505929cd53d85410054164a73d4b6150401505929cd52d8541004c164a83d87515040130592a0f615454100407e5984dc9538c40185165600714c931004836538254d620c40120d94e1d5358831004916478754d620c40120d942015358831004916448054d620c4016079154d62504310068160d62d45410c40160593d51625043100581e5153589410c4016059590d62504310058165543589410c40130592e1d535043100485e598754d410c40121698dd953504310044565f8254d410c401115972015350431004c16488054d410c4016079254d625043100581e5953589410c401225989d562504310058164e75589410c40160595a0d62504310058165673589410c4016079854d625043100581e5d53589410c4016059754d62504310058124153589410c4018258758b52504310068160d62d49410c4018858758b32504310068161562cc9410c401c057558941cc431007015d562505310c401e01535894198031004866508054d600c4012499220153580310058424153505600c4016139654d415803100684e1953505600c401e015398941580310078054d62505600c4012199421d5358031004926488754d600c4012519121d5358031004866538254d600c40125191e09535803100584e4553505600c40161193d4541580310058464f54505600c4016139454d41580310058465643505600c4016819290d41580310058465543505600c40161193a15415803
  | 3 => 0x90db81aa9302289da112047902600368b32f475234be2383c33800035004010141d0040000000014080240400005018000140a00000014020080105c01018020140903c2b0280b00c0c02007038000000200002028020000503c0c048010080a034090a000040000140001400070000300f0142a0200806c01040060000504c04000030b800028000000e0100000c06008050240000c09030000000c04c0001000000010140300402000090001100c010000f01806004000140900c0101402004000280201c01054020380e01000030000140d00503a4b845cf615500142591211721815400603211835c8605500141691e0d74d895300605610835c46054c014459220d71181530048364a83dc564d480140d92a0f71593520048564f81551611080121593e1d54584420048964b875516110801215932015458442004896488055161108012199320154580420048c6448055160108012199321d54580420048a6488755160108012319121d54580420048664f81551601080122992e0554580420068255183909601080141593a1571993320050964a855c664cc80103591e1974d4b320050565a855c664cc80150592a15719933200445647865d352cc80130591a137254d3200541e4d545c4424c80150594d4d711093200541657435c4424c8015059550d711093200542e4d545c0424c80150994d4d701093200542657435c0424c80158191d0d701093200542655435c0424c801505919d353cc932005416467454f324c8019058460971995320046164684dc9654c80130591a1372595320054164684dc9654c8019067560674d8932006415d5819d3624c8015059199674d893200641a15819d3624c8019058560674d893200641a55819d3624c8019059560674d893200641995819d3624c8019056560674d89320054164674d53624c801505919d154d8932004c164684d8b524c80130591a13625493200541e49545c4424c80150594d49711093200541655425c4424c80150b92551701093200542653525c0424c801509955097010932004c164786550424c80110f97619541093200443a6276550424c80120d96e0554109320048365880550424c80130591201541093200541e45545c4424c801505959d1711093200541e5d545c4424c80114598995711093200541652655c4424c80150595a11711093200541656645c4424c80150798551711093200541e59545c4424c80150596551711093200541241545c4424c801d01545c6701093200542241545c0424c801509959d1701093200542e5d545c0424c801c0a76551701093200740552715c0424c801d01545c5701093200550644855c0424c80150994995701093200550646655c0424c80150995991701093200560646645c0424c80150898551701093200542e59545c0424
  | 4 => 0x184a38be0d99a582f0252907002ea280000000559d0af218cf810db1ae00040cd02a8a848ab9d2a50b26991e7992e001c46800064800000000000000232b70000027a169dc0e102158e8cf30083800c735c9804cd81581399c9088412b64002481c80097800002d61f800c5b226a8000010a10800c19781d0000017ed29620000023800508ea00070b68fa868a849878ae800002ee9a0d4af8008a3321e80000000510e200000ddb2c9f1322e00014000000000031a000689033a8c000a7172b7ab4d0a920024c1f09cb10e45c12ca780033996d3a80dc16cb81ac5d95e9a8006c81e4615c0925a3d00087800000000000000000948006d000001a4368007083aae1fc4e800002e260000523726f274ac020760626794600000000000025648a00300000010c22000928b6262100022000374002ca00000002588d98a0020c0cb5800000c79106c000b20cc7da5c258ae94214789686f98800140191fac38c299800ca2126a1eab3904aa2844e278d58a0c9800adae60023a3806a8b2160b350d1000d5000d6930492ac7580053206618007c98222b5ec498ec22e85524441882c5014780760006672a2e873183f0c8118a48f950003629dac6000de000928f24601800da800001947b016000000012a451f84f052d48000009a5900443b3071aa2b41287c0005480000000890000f800403660d17c9b8f8b09f4ca80c68b40003200000000000328bcb9054038dcbc80000000000122316e000f6d31de732269c262318860017a00000000002d01c00000528000003000000481369c8e6241746da822c000000580000002800361983b002d186e9391a0030a342c00002818000000005393e00000a62faa99121b0c4298d20f25482008b51086e1347fa6c6e800bf8f208b48a6a02bb2a0992fcac8187a2ea45a22b60baaaad27220ac118cc30d69fa8c3f8ac2ab100015abda967385e47336cba881716a279eec90803b966a19
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x10008000064011004d7a7007c0000015500000000000a0ea30050f26004802d2c0000f0000c0a4030301040048000694801a015955c0108038002003600b80582c3a5480070344085060204000000010306101000100500b4242306b90c0aa00300584648835c46054c01402d352ac0ce9b12640090169b98551711093200420b51cb2a8b888499002405a6241545c4424c801280d0920aa2e02126400902698985517010932004a03424c2a8b808499002501a1e59545c0424c801204d3722aa2e0212640090168694e09764cb5100480b4549f02bb6a4a0802805a6a55829cf6150401202d3f30a9ac4a0862008816a39754d625043100480b4e482a6b128218802601a224153505600c401300d1730a9a82b0062008846a09754d4158031004c03444baa6a0ac018802211a8e4953505600c401202d0d29c3ae6b10a000a016868460976cc85000480b434a704bb264280030057664684dc93214001102d0f30b26e4990a00090168a93e1d745845000480b4f4a704992c228002805a2a0d815db4114001202d1527c0aeca08a000c015d992a0f715045000440b45cc2c7b8a8228002205a9a0d62dc54114001102d092cc26a4992400088168496612754c92000500b4f4ab023226490002205a99d5811913248001802c3b2232265a8a4000c0161d91191321412000500b5032264b88a090002205a225983d454144001102d112cc1ceaa0a2000a0169e95608635051000440b533ab0431a82880030058764863d494144001802c3b2431a8228220009016a4635c94114110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 74
  | 6 => 2395
  | 5 => 7024
  | 4 => 2631
  | 3 => 444
  | 2 => 48
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (2092+((h/24+packedAt gbK7 (1924+(h % 24)*7) 7) % 89)*8) 8
  | 6 => packedAt gbK6 (98191+((h/798+packedAt gbK6 (88615+(h % 798)*12) 12) % 3162)*13) 13
  | 5 => packedAt gbK5 (369926+((h/2341+packedAt gbK5 (337152+(h % 2341)*14) 14) % 8429)*14) 14
  | 4 => packedAt gbK4 (165753+((h/877+packedAt gbK4 (155229+(h % 877)*12) 12) % 3473)*13) 13
  | 3 => packedAt gbK3 (32560+((h/148+packedAt gbK3 (31080+(h % 148)*10) 10) % 586)*10) 10
  | 2 => packedAt gbK2 (4000+((h/16+packedAt gbK2 (3888+(h % 16)*7) 7) % 82)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0fff8c183e1c0ff87f03f83f08d278474cf
  | 1 => 0xf07f0f0701fc3e00f0f87fc3fc734ada1a4b33
  | 2 => 0x7ff007fe003fff00ff8003ff8c731c638c3c
  | 3 => 0xff800007ffffc00000fffffc000f83e07c0fc0
  | 4 => 0x7ffffffffff000000000ffc007ff000
  | 5 => 0xfffffff80000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x801100000040401000900080000000801045
  | 1 => 0x10310a1200a43204a20825013061484a0a4112
  | 2 => 0x844aa0215200049200d5008a4b041314208c28
  | 3 => 0xad088045f54a800a04e64ab8090e83a0740e80
  | 4 => 0x8100886a9f3392cce000310102bec005f6000
  | 5 => 0xce7cccf03062103088440c20624fffff000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_11894
namespace PEqualNP.Outside.L_meta_11894
open PEqualNP.Outside.L_meta_11894.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 48 := (concat bgb_2_0 bgb_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_320 : Interval gbAtlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_352 : Interval gbAtlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_384 : Interval gbAtlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_416 : Interval gbAtlas 3 416 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 444 := (concat (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192))) (concat (concat bgb_3_224 (concat bgb_3_256 bgb_3_288)) (concat (concat bgb_3_320 bgb_3_352) (concat bgb_3_384 bgb_3_416))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2631 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)))) (concat (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 (concat bgb_4_416 bgb_4_448))) (concat (concat bgb_4_480 bgb_4_512) (concat bgb_4_544 (concat bgb_4_576 bgb_4_608))))) (concat (concat (concat (concat bgb_4_640 bgb_4_672) (concat bgb_4_704 (concat bgb_4_736 bgb_4_768))) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 (concat bgb_4_896 bgb_4_928)))) (concat (concat (concat bgb_4_960 bgb_4_992) (concat bgb_4_1024 (concat bgb_4_1056 bgb_4_1088))) (concat (concat bgb_4_1120 (concat bgb_4_1152 bgb_4_1184)) (concat bgb_4_1216 (concat bgb_4_1248 bgb_4_1280)))))) (concat (concat (concat (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 (concat bgb_4_1408 bgb_4_1440))) (concat (concat bgb_4_1472 bgb_4_1504) (concat bgb_4_1536 (concat bgb_4_1568 bgb_4_1600)))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 (concat bgb_4_1728 bgb_4_1760))) (concat (concat bgb_4_1792 (concat bgb_4_1824 bgb_4_1856)) (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952))))) (concat (concat (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 (concat bgb_4_2080 bgb_4_2112))) (concat (concat bgb_4_2144 bgb_4_2176) (concat bgb_4_2208 (concat bgb_4_2240 bgb_4_2272)))) (concat (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 (concat bgb_4_2400 bgb_4_2432))) (concat (concat bgb_4_2464 (concat bgb_4_2496 bgb_4_2528)) (concat bgb_4_2560 (concat bgb_4_2592 bgb_4_2624)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6304 : Interval gbAtlas 5 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6368 : Interval gbAtlas 5 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6400 : Interval gbAtlas 5 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6464 : Interval gbAtlas 5 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6496 : Interval gbAtlas 5 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6560 : Interval gbAtlas 5 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6592 : Interval gbAtlas 5 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6656 : Interval gbAtlas 5 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6688 : Interval gbAtlas 5 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6752 : Interval gbAtlas 5 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6784 : Interval gbAtlas 5 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6848 : Interval gbAtlas 5 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6880 : Interval gbAtlas 5 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6944 : Interval gbAtlas 5 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6976 : Interval gbAtlas 5 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 7024 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)))) (concat (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)))))) (concat (concat (concat (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920))) (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144)))) (concat (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592))))) (concat (concat (concat (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat (concat bgb_5_2944 bgb_5_2976) (concat bgb_5_3008 bgb_5_3040)))) (concat (concat (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)) (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264))) (concat (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)) (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 bgb_5_3488))))))) (concat (concat (concat (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 bgb_5_3904)))) (concat (concat (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000)) (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 bgb_5_4128))) (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat (concat bgb_5_4256 bgb_5_4288) (concat bgb_5_4320 bgb_5_4352))))) (concat (concat (concat (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448)) (concat (concat bgb_5_4480 bgb_5_4512) (concat bgb_5_4544 bgb_5_4576))) (concat (concat bgb_5_4608 (concat bgb_5_4640 bgb_5_4672)) (concat (concat bgb_5_4704 bgb_5_4736) (concat bgb_5_4768 bgb_5_4800)))) (concat (concat (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)) (concat (concat bgb_5_4928 bgb_5_4960) (concat bgb_5_4992 bgb_5_5024))) (concat (concat bgb_5_5056 (concat bgb_5_5088 bgb_5_5120)) (concat (concat bgb_5_5152 bgb_5_5184) (concat bgb_5_5216 bgb_5_5248)))))) (concat (concat (concat (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat bgb_5_5376 (concat bgb_5_5408 bgb_5_5440))) (concat (concat bgb_5_5472 (concat bgb_5_5504 bgb_5_5536)) (concat (concat bgb_5_5568 bgb_5_5600) (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat (concat bgb_5_5792 bgb_5_5824) (concat bgb_5_5856 bgb_5_5888))) (concat (concat bgb_5_5920 (concat bgb_5_5952 bgb_5_5984)) (concat (concat bgb_5_6016 bgb_5_6048) (concat bgb_5_6080 bgb_5_6112))))) (concat (concat (concat (concat bgb_5_6144 (concat bgb_5_6176 bgb_5_6208)) (concat (concat bgb_5_6240 bgb_5_6272) (concat bgb_5_6304 bgb_5_6336))) (concat (concat bgb_5_6368 (concat bgb_5_6400 bgb_5_6432)) (concat (concat bgb_5_6464 bgb_5_6496) (concat bgb_5_6528 bgb_5_6560)))) (concat (concat (concat bgb_5_6592 (concat bgb_5_6624 bgb_5_6656)) (concat (concat bgb_5_6688 bgb_5_6720) (concat bgb_5_6752 bgb_5_6784))) (concat (concat bgb_5_6816 (concat bgb_5_6848 bgb_5_6880)) (concat (concat bgb_5_6912 bgb_5_6944) (concat bgb_5_6976 bgb_5_7008))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2395 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))))) (concat (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))) (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 74 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffeeeeffffeeeefefaeeeafefaeee8ffffeeeeffffeeeefefaeeeafefaeee8ffffeeeeffffeeeefefaeeeafefaeee8ffffeeeeffffeeeefefaeeeafefaeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) SB :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 7) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 7 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_11894.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.or,[7,5]⟩,⟨.and,[8,6]⟩,⟨.or,[0,1]⟩,⟨.or,[10,2]⟩,⟨.or,[5,6]⟩,⟨.and,[11,12]⟩,⟨.or,[0,1]⟩,⟨.and,[14,4]⟩,⟨.or,[9,13]⟩,⟨.or,[16,15]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,17,monoShape,by change 11 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_11894

open PEqualNP.Outside.L_meta_11894 in
theorem PEqualNP.Outside.L_meta_11894 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
