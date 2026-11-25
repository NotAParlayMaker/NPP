import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14530.Model
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_14530.Model

namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
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

def SB : Nat := 3

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

end PEqualNP.Outside.L_meta_14530

namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def s0K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (5+((h/1+packedAt s0K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdfc73ffc707ff33f
  | 2 => 0xffffffffffffffffffffffeff83fff807ffc3f
  | 3 => 0x77ffc73fff8e0fcc
  | 4 => 0x7bfff83ffff00ff0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa07052141512a315
  | 2 => 0x1086a4288a254c2a
  | 3 => 0x912304d2308654c
  | 4 => 0x62406b24c418ab0
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def s1K2 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (6+((h/1+packedAt s1K2 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff0f83fffff8307fffffc1c1ffff87f0ff
  | 2 => 0xf0f83ff003c3c3ffc070e1f0fe01e3c7e54c93
  | 3 => 0xff003ffffc03fc1fff80fe00fffe03f8798f1c
  | 4 => 0x3ffffffc001fffff0000fffffc007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10000100040000000001021000402040001025
  | 2 => 0x2636722369a5a719cc3871a2f20d4a97654c92
  | 3 => 0x42529445208a212a5480b48454940331298518
  | 4 => 0x8a5288a42208a54a95a0108a9299802560ac0
  | 5 => 0x8cc630ec7333339f3e6cd9ce303112247fe000
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 61 s1Pos s1Neg, 0xffaaaaaaffaaaaa0ffaaaaaaffaaaaa0ffaaaaaaffaaaaa0ffaaaaaaffaaaaa0ffaaaaaaffaaaaa0ffaaaaaaffaaaaa0ffaaaaaaffaaaaa0ffaaaaaaffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def s2K2 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (6+((h/1+packedAt s2K2 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff0f83fffff8307fffffc1c1ffff87f0ff
  | 1 => 0xf0f83ff003c3c3ffc070e1f0fe01e3c7e54c93
  | 3 => 0xff003ffffc03fc1fff80fe00fffe03f8798f1c
  | 4 => 0x3ffffffc001fffff0000fffffc007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10000100040000000001021000402040001025
  | 1 => 0x2636722369a5a719cc3871a2f20d4a97654c92
  | 3 => 0x42529445208a212a5480b48454940331298518
  | 4 => 0x8a5288a42208a54a95a0108a9299802560ac0
  | 5 => 0x8cc630ec7333339f3e6cd9ce303112247fe000
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 59 s2Pos s2Neg, 0xffaaaaaaffaaaa88ffaaaaaaffaaaa88ffaaaaaaffaaaa88ffaaaaaaffaaaa88ffaaaaaaffaaaa88ffaaaaaaffaaaa88ffaaaaaaffaaaa88ffaaaaaaffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def s3K2 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s3K2 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s3K2 (6+((h/1+packedAt s3K2 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 1 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 2 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 1 => 0x1212522244a90309434290a252144943294512
  | 2 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s3Atlas : Atlas := ⟨2,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def s4K2 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s4K2 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s4K2 (6+((h/1+packedAt s4K2 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 1 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 2 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 3 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 1 => 0x1212522244a90309434290a252144943294512
  | 2 => 0x2124a4442952103298852a04a5409298528a28
  | 3 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s4Atlas : Atlas := ⟨2,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8eaeaeaeaeae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def s5K2 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s5K2 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s5K2 (6+((h/1+packedAt s5K2 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 3 => 0x488c032520240c92352918000e498192540f80
  | 4 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s5Atlas : Atlas := ⟨2,rawDecor 31 s5Pos s5Neg, 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8c909c881cc414c055003498d4b8b01000f0d0846c285c51140060b4004ca074ec2000e5100c00ac2ce8a80478307ccc000038003c58000000940000007000bd08d80800a480450c24c8e0fc406904dcf4f864481840019003468a0000280081439600047023204200007fd50017f54007f95001fd54005f55001fc54007fd4c017f53007f94c01fd53005f54c01fc53007fd0c01fe43007f50c01fc43007fd48017f52007f94801fd52005f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd44017f51007f94401fd51005f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd4001fe50005f94001fd50007f140017c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x284000bf99420006fcca100027e65080017eb284000df59420004faca10002fc65080017fb204000bf990200077cc810002be64080017eb204000ef590200057ac810002fc6408001bfaa04000df55020005fec610002fe6308001ef3184000b798c20005fac610003dd63080016eb184000bf18c20006fea6100037d53080017f3104000dfd4820006faa410002fe6108001fb3084000bd98420005fac210003f561080017ab084000dfd4420006faa210003ee2108001f61084000bf98020006fca0100037c5008001f79004000fe88020007da4010003f920080017fb2e2000bf99710006fccb880027e65c40017eb2e2000df59710004facb88002fc65c40017fb262000bf99310005fac988002fc64c4001bfaa62000df55310005fec788002fe63c40017eb1e2000bf18f10006fea7880037d53c40017fb162000bf98b10005fac588002fc62c4001bfa962000df54b10006fea388003f651c4001bea8e2000fd54710006eaa388003f641c4001faa0e2000fd8c710007ea6388003f621c4001fa90e2000df94310006f8a188002ff6584001bfb2c20009fd9610005fccb08002fd65840017e32c2000df19610004f8cb08002ff64840017f3242000bf59210005f8c9080037f5484001beaa42000bfd8e10005fcc708002fd63840017e31c2000dfd4e10006faa708002ff62840017f3142000bf58a10005f8c5080037f5284001bea942000bf58610006fea3080037d5184001fb90c2000fd08610005fcc1080037e5084001be2842000fe88210007f24108003f71084001fd8842000bfd9510006feca880027f65440017f32a2000bf59510005f8ca880037c65440013e32a2000bfd9110005fcc888002fd64440017e3222000dfd5110006faa888002ff63440017f31a2000bf58d10005f8c6880037f5344001bea9a2000bfd8910007dec488002ef62440017f3122000bf58910005f8c488003ec6244001763122000dfd4910006faa4880037f5144001fb28a2000df54510007eaa288003755144001fb20a2000fd50510007ec6288003f53144001fb10a2000fd48510006fca0880037c5044001fd1022000fe48110007f62088003f610440017fb282000bf99410006fcca080027e65040017eb282000df59410004faca08002fc65040017fb202000bf990100077cc808002be64040017eb202000ef590100057ac808002fc6404001bfaa02000df55010005fec608002fe6304001ef3182000b798c10005fac608003dd63040016eb182000bf18c10006fea6080037d53040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc6204001bfa902000df54810005fcc2080037f5104001bea882000fdc8410007e84208002fe6004001bf2802000df14010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x37d538c001efa1c6000f710e30005fcc518002fd628c001bfa946000df54a30005fcc318002fd618c001bfa8c6000df54630005fcc1180037e508c001be2846000fe90230007f28118003df308c001fd9846000bfd9530006feca980027f654c0017f32a6000bf59530005f8ca980037c654c0013e32a6000bfd91300077ec898002bf644c0017f3226000bf59130005f8c898003bc644c0015e3226000dfd5130006faa8980037f534c001ef29a6000df54d30007baa6980035d534c001ef21a6000f750d30005fec498002fc624c001bfa926000df54930007be6498003dd324c0017fb0a6000bf18530006fea2980037d514c001ef98a6000f74c530006fca0980037c504c001fd2026000fe50130007f66098003de304c0017fb286000bf99430006fcca180027e650c0017eb286000df59430004faca18002fc650c0017fb206000bf990300077cc818002be640c0017eb206000ef590300057ac818002fc640c001bfaa06000df55030005fcc6180037f530c001bea986000f7d0c30007b88618002fe620c001f73106000bb98830005fac418003ed620c00176b106000dfd4830006faa418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000dfd4430006faa218002fe600c001bf2806000df14030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c8001bf32e40009f99720005facb900037d65c80013eb2e4000bf19720005fec990002fe64c80017eb264000bf19320006fea9900037d54c80017fb1e4000bf98f20005fac790002fc63c8001bfa9e4000df54f20006fea590003ee52c8001bea964000fb54b20006daa590003ee42c8001f6a164000fb8cb20007da6590002fe61c80017eb0e4000dfd4720006faa390003ef21c8001f690e4000df94320006f8a190002ff6588001bfb2c40009fd9620005fccb10002fd65880017e32c4000df19620004f8cb10002ff64880017f3244000bf59220005f8c9100037f5488001beaa44000bfd8e20005fcc710002fd63880017e31c4000dfd4e20006faa710002fd6288001bfa944000df54a20005fcc310002fd6188001bfa8c4000df54620007dc4310003ec21880017f3044000df94220006f8a110003ef2088001fd9044000bfd9520006feca900027f65480017f32a4000bf59520005f8ca900037c65480013e32a4000bfd9120005fcc890002fd64480017e3224000dfd5120006faa890002ff63480017f31a4000bf58d20005f8c6900037f5348001bea9a4000dfd4920007dca4900037d5248001f6a924000db54920007dc8490003ed4248001f71924000fb4c920005fec290003f761480017bb0a4000bf18520007e8c290002f46148001bfa8a4000df54520007de4290003ed2148001bf2824000df14120007f64090003ee20480017fb
  | 2 => 0x50006f864280037f6114001bf308a000dd98450006fac2280027d6114001bab08a0009d58450006f8c2280037f4114001bf208a000df50450006f882280037f3114001bf188a000df4c450006f862280037f2114001bf108a000df48450006f842280037e60140013f300a000de98050005fecba0002fe65d0001bf32e80009f99740005facba00037d65d00013eb2e8000bf19740006fea9a0003be54d0001beaa68000ef553400067aa9a0002fe63d00017eb1e8000dfd4f40006faa7a0003bf43d0001dea1e8000bf98b40005fac5a00037f52d0001bea968000efd0b400077a85a0002fe61d00017eb0e8000dfd4740006faa3a0003bf41d0001dea0e8000df94340006f8a1a0002ff6590001bfb2c80009fd9640005fccb20002fd65900017e32c8000df19640004f8cb20002fd6490001bfaa48000df55240005fcc720002fd6390001bfa9c8000df54e400077c8720003bc43900017f3148000bf58a40006fea5200037d52900017f30c8000bf58640006fea3200037d51900017f3048000df94240006f8a120003bf4090001fda048000bfd9540006fecaa00027f65500017f32a8000bf59540005f8caa00037c65500013e32a8000dfd51400077ca8a00037d5450001deaa28000cf55140005fec6a0003df63500016fb1a8000bf18d40007b8c6a0002dc6350001bfa9a8000df54d400077e86a0003bd43500017fb128000bf18940006fea4a00037d5250001dfa128000ef50940005fec2a0002fc6150001bfa8a8000df545400077e82a0003bd4150001bf2828000df14140007f680a0003be40500017fb288000bf99440006fcca200027e65100017eb288000df59440004faca20002fc65100017f3208000dfd5040006faa820002fe6310001ef3188000b798c40005fac620003dd63100016eb188000dfd4c40006faa620003be4310001de2188000bf98840007dcc420002ee62100017eb108000fb58840005dac4200037f5210001bea908000bf98440007ecc220002f661100017eb088000fd58440005eac2200037f5110001bea888000bf98040006fca0200037c5010001dfa008000fe900400077a8020003f940100017fb2e6000bf99730006fccb980027e65cc0017eb2e6000df59730004facb98002fc65cc0017fb266000bf99330005fac998002fc64cc001bfaa66000df55330006fea798003de53cc001bea9e6000f754f30006baa798003de43cc001eea1e6000bf98b30005fac5980037f52cc001bea966000f7ccb30007ba6598002fe61cc0017eb0e6000dfd4730006faa398003df31cc001ee98e6000df94330006f8a198002ff658c001bfb2c60009fd9630005fccb18002fd658c0017e32c6000df19630004f8cb18002ff648c0017f3246000bf59230005f8c9180037f548c001beaa46000bf58e30006fea71800
  | 3 => 0xe3184200dfd4c21006faa610802fe6208401bfa904200fb94821006faa410803ed5208401b6a904200fb90821007da8410803ee3208401f69904200bf98421006fea210803f65108401bea884200fd54421006eaa210803f64108401faa084200fd8c421007ea6210803ef2108401fb1084200fb48421007ea4210803e521084017f3004200fe98021005f4c010802fd6008401fcb004200be58021005fcc9a8002fd64d4001bfaa6a000df55350005fcc7a8002fd63d4001bfa9ea000df54f50005fcc5a8002fd62d4001bfa96a000df54b50005fcc3a8002fd61d4001bfa8ea000df54750005facb28002fe64940017eb24a000dfd5250006fca9280037d5494001be2a4a000bf98e50005fac7280037f5394001bf29ca000df54e50006f8a728002fe62940017eb14a000dfd4a50006fca5280037d5294001be294a000bf98650005fac3280037f5194001bf28ca000df54650006f8a328002fe6094001bfa84a000fed4250006fec9280037e6494001beb24a0009f59250006f8c9280037f6394001bf31ca000df58e50004fac7280037c6394001bfa1ca000df90e50006fa87280037c4394001bfb14a000df98a50006fac5280027d6294001be314a000dfd0a50006fc85280037d4294001be214a000dfcca50006fc65280037d3294001be194a000dfd8650006fcc3280037d61940013eb0ca000df18650006fe83280037e4194001bea0ca000df10650006fe63280037e3194001be98ca000df0c650006fe43280037e2194001be90ca000df08650004fcc128002ff64540017e322a000dfd5150006faa8a8002ff63540017e31aa000dfd4d50006faa6a8002ff62540017e312a000dfd4950006faa4a8002ff61540017e30aa000dfd4550006faa2a8003fb5054001bf282a000bf99450005fcc828003be64140015f320a000bf590500077ac828002bd6414001bfaa0a000df95050006faa8280037c54140017f318a000f798c50005bcc628002fd6314001eeb18a000b758c50006fea6280037e5314001bea98a000df14c50005fcc428003ee621400177310a000bf58850007dac428002ed6214001bfa90a000df94850006faa4280037c52140017f308a000fd98450005ecc228002fd6114001fab08a000bd58450006fea2280037e5114001bea88a000df14450005fcc0280037f5014001fd280a000df54050007f2a0280037f6414001bf320a000cf99050006fac8280027d64140019eb20a0008f59050006f8c8280037f6314001bf318a000d798c50006fac6280027d6314001aeb18a0009758c50006f8c6280037f4314001bf218a000df50c50006f886280037f6214001bf310a000db98850006fac4280027d6214001b6b10a0009b58850006f8c4280037f4214001bf210a000df50850006f884280037f3214001bf190a000df4c8
  | 4 => 0x802fe60cc4017eb066200bfd9631005fccb188037e658c4013f32c6200bf59631006facb188027d658c4017e32c6200bfd9231005fcc918803be648c4015f3246200bf592310077ac918802bd648c4017e3246200dfd5231006faa918802fd638c401bfa9c6200df54e31005fcc518802fd628c401bfa946200df54a31005fcc3188037f518c401bea8c6200fd90631007ea8318803df318c401fb98c6200bf98231005fac118802ff654c4017f32a6200df99531004fcca98802fd654c401beb2a62009f59531005f8ca98802ff644c4017f3226200bf59131005f8c8988037f544c401beaa26200dfd4d31006faa698803df434c401ee21a6200bfd8931005f8c4988037f524c401bea926200f7cc931007ba64988037f514c401bea8a6200fd90531007ea8298803f7314c401ef18a6200bfd8131005f8c098802ff650c4017f3286200df99431004fcca18802fd650c401beb2862009f59431005f8ca18802ff640c4017f3206200bf59031005f8c8188037f540c401beaa06200bf98c31006fea6188037d530c4017f3106200bf58831006fea4188037d520c4017f3086200dfd4431006faa218803df310c401fb1886200f74c431007ea6218802fe600c4017eb006200bfd9721005fccb908037e65c84013f32e4200bf59721006facb908027d65c84017e32e4200bfd9321005fcc990802fd64c84017e3264200dfd5321006faa990802ff63c84017f31e4200bf58f21005f8c7908037f53c8401bea9e4200dfd4b21006faa5908037f51c8401fb28e4200df54721007eaa3908037551c8401fb20e4200fd50721007ec6390803f531c84017f3064200bf58321005fecb10802fe6588401bf32c42009f99621005facb108037d65884013eb2c4200bf19621005fec910802fe64884017eb244200bf19221006fea9108037d54884017fb1c4200bf98e21005fac710802fc6388401bfa9c4200df54e21005fac5108037f5288401f72944200df54a21007daa5108036d5288401f72144200fb50a21007dc6510803ed32884017f30c4200dfd4621006faa310803ef2188401fb90c4200bf98221005fac110802ff65484017f32a4200df99521004fcca90802fd6548401beb2a42009f59521005f8ca90802ff64484017f3224200bf59121005f8c8908037f5448401beaa24200bfd8d21005fcc690802fd63484017e31a4200dfd4d21006faa6908037f5248401bea924200dfd4521006faa290803f72148401f710a4200bfd8121005f8c090802ff65084017f3284200df99421004fcca10802fd6508401beb2842009f59421005f8ca10802ff64084017f3204200ef990210057cc810802fd6408401deb204200af59021005f8c8108037f5408401beaa04200bfd8c21005fcc610803de63084016f3184200bf58c21007bac610802dd63084017
  | 5 => 0x9151006fea8a88037e5454401beaa2a200df15151005fec6a8802fc6354401bfa9aa200df94d51006faa6a88037c53544017fb12a200bf18951006fea4a88037e5254401bea92a200df14951007eea2a88037e51544017fb02a200bf18151006fec8a88027f6454401bf322a200df59151006f8c8a88037f63544013fb1aa200df98d51006fac6a88037c6354401bfa1aa200df90d51006fa86a88037c4354401bfb12a2009fd8951006fcc4a88037d6254401be312a200dfd0951006fc84a88037d4254401be212a200dfcc951006fc64a88037d3254401be192a200dfd8551006eec2a88037f6054401bf302a200df58151006f8c0a88027c60544017f328a2009f99451005fcc828802fd6414401bfaa0a200df55051005fcc628802fd6314401bfa98a200df54c51005fcc428802fd6214401bfa90a200df54851005fcc2288037f5114401fb288a200df54451007eaa228802fe60144017eb00a200bfd9741005fccba08037e65d04013f32e8200bf59741006facba08027d65d04017e32e8200dfd5341006faa9a0802fe63d04017eb1e8200dfd4f41006faa7a0803be43d0401de21e8200bf98b41007dcc5a0802ee62d04017eb168200fb58b41005dac5a08037f52d0401bea968200efd0b410077a85a08037f51d0401bea8e8200bf98341005fac1a0802ff65904017f32c8200df99641004fccb20802fd6590401beb2c82009f59641005f8cb20802fd6490401bfaa48200df55241005fcc720803de63904016f31c8200bf58e41007bac720802dd6390401bfa9c8200df54e41005fcc520802fd6290401bfa948200df54a41005fcc3208037f5190401bea8c8200efd0641007ee8320802fe60904017eb048200bfd9541005fccaa08037e65504013f32a8200bf59541006facaa08027d65504017e32a8200dfd5141006faa8a0802ff63504017e31a8200dfd4d41006faa6a0803be4350401de21a8200bfd8941005f8c4a08037f5250401bea928200efd09410077a84a08037f5150401bea8a8200fdd05410077c82a0802ff60504017e3028200bfd9441005fcca208037e65104013f3288200bf59441006faca208027d65104017e3288200bf99041006fea8208037d54104017f3188200bf58c41006fea6208037d53104017f3108200bf58841006fea4208037d52104017f3088200dfd4441006faa220803bf4110401fb2088200ef50441007ea8220802fe60104017eb008200bfd9731005fccb988037e65cc4013f32e6200bf59731006facb988027d65cc4017e32e6200bfd9331005fcc998802fd64cc4017e3266200dfd5331006faa9988037f53cc401bea9e6200f7d0f31007b88798802fe62cc401f73166200bb98b31005fac598803ed62cc40176b166200dfd4b31006faa598803df32cc401ee9966200dfd4731006faa398
  | 6 => 0x17fb288400bf99442006fcca210027e65108017eb288400df59442004faca21002fc65108017f3208400dfd5042006faa821002fe63108017eb188400dfd4c42006faa621002fe6210801bfa908400df548420077e8421003ee4210801dea108400fb50842005fcc221002fd61108017f3008400bf58042005fecb99002fe65cc801bf32e64009f99732005facb990037d65cc8013eb2e6400bf19732005fec999002fe64cc8017eb266400bf19332006fea9990037d54cc801bfa9e6400df54f32007be8799003dc43cc801bfa966400df54b32005fcc399003f661cc8017b30e6400bf58732007eac399002f561cc8017f3066400bf58332005fecb19002fe658c801bf32c64009f99632005facb190037d658c8013eb2c6400bf19632005fec919002fe648c801df3246400af99232005fac919003bd648c8015eb246400bf19232006fea9190037d548c8017eb1c6400dfd4e32006faa719002fe628c801bfa946400df54a32007dc8519003ed428c801ef9946400fbcca32005fcc319002fd618c8017f3046400bf58232005feca99002fe654c801bf32a64009f99532005faca990037d654c8013eb2a6400bf19532005fec899002fe644c8017eb226400bf19132006fea8990037d544c801bfa9a6400df54d32007be8699003dc434c801bfa926400df54932007dc8499003ed424c801f79926400f78c932005fec299002fc614c8017fb026400bf18132005feca19002fe650c801bf32864009f99432005faca190037d650c8013eb286400bf19432005fec819002fe640c8017eb206400bf19032006fea8190037d540c8017f3186400dfd4c32006faa619002fe620c801bfa906400df54832007be6419003ee320c801ee9906400fb4c832005fcc219002fd610c8017f3006400bf58032005fcc9a8802fd64d4401bfaa6a200df95351006faa9a88037c54d44017f31ea200bf58f51006fea7a88037e53d4401bea9ea200df14f51005fcc5a8803ee62d440177316a200bf58b51007dac5a8802ed62d4401bfa96a200df94b51006faa5a88037c52d44017f306a200bf58351006fec9a88037e64d4401beb26a2009f59351006f8c9a88037f63d4401bf31ea200df58f51004fac7a88037c63d4401bfa1ea200df90f51006fa87a88037c43d4401bfb16a200df98b51006dcc5a88037d62d44013eb16a200db58b51004dac5a88037c62d4401bfa16a200df90b51006fa85a88037c42d4401bf996a200df8cb51006fa65a88037c32d4401bfb06a200df98351004fcc1a88037d60d4401be306a200bf59651004facb28802fe64944017eb24a200dfd5251006faa928802fe63944017eb1ca200dfd4e51006faa728802fe62944017eb14a200dfd4a51006faa528802fe6194401bfa8ca200fdd4651005fcc128802fd60944017fb22a200bf1
  | 7 => 0x21802ee6210c017eb108600fb58843005dac421802fe6110c01fb3088600bd98443005fac221803f56110c017ab088600bf98043007f4c021802fa6010c017eb008600fe58043005f2c021802fe64d48017eb26a400dfd5352006fca9a90037d54d4801be2a6a400bf98f52005fac7a90037f53d4801bf29ea400df54f52006f8a7a9002fe61d4801fb30ea400bd98752005fac3a9003f561d48017ab0ea400bf98352005fac1a90037f64d4801bf326a400df59352004fac9a90037c64d4801bfb1ea400df98f52006fac7a90027d63d4801be31ea400dfd0f52006fc87a90037d43d4801be21ea400dfd8752006fcc3a90037661d4801beb0ea4009f58752006eac3a90027561d4801be30ea400dfd8352006fcc1a90027e60d4801beb06a400df18352005facb290027d65948017f324a400bf59252006fea9290037d54948017f31ca400bf58e52006fea7290037d53948017f314a400dfd4a52007dea529002fe61948017eb0ca400bf98252005fac129002ff64548017e322a400dfd5152006fca8a90037d5454801be2a2a400bfd8d52005f8c6a90037f5354801bf29aa400df54d52006f8a6a9003ef5254801bf292a400bfd8552005f8c2a9002ff60548017e302a400dfd9152004fec8a90037e6454801beb22a400df19152006fec6a90027f6354801bf31aa400df58d52006f8c6a90037f4354801bf21aa400df50d52006f886a90037f6254801b7b12a400dfd8552004fec2a90037e6154801beb0aa400df18552006fec0a90037e6054801beb02a400df18152004f8c0a9002fe65148013f328a400bf99052005fac8290037f5414801beaa0a400bf98c52005fac6290037f5314801bea98a400bf98852006fea429003ee5214801bea90a400fb54852005fcc229002fd61148017f300a400bf58052005fecba1002fe65d0801bf32e84009f99742005facba10037d65d08013eb2e8400bf19742006fea9a10037d54d08017f31e8400bf58f42006fea7a10037d53d0801df21e8400ef10f42006fea5a10037d52d08017f30e8400fd98742005ecc3a1002fd61d0801fab0e8400bd58742005fcc1a1002fd60d08017fb2c8400bf99642006fccb210027e65908017eb2c8400df59642004facb21002fc65908017eb248400dfd5242006faa921002fe6390801ef31c8400b798e42005fac721003dd63908016eb1c8400dfd4e42006faa721002fe6290801bfa948400df54a420077e8521003ef42908017f30c8400bf58642005fcc121002fd60908017fb2a8400bf99542006fccaa10027e65508017eb2a8400df59542004facaa1002fc6550801bfaa28400df55142005fec6a1002fc6350801bfa9a8400df54d420077c86a1003bc4350801bfa928400df54942007de84a1003be42508017fb0a8400bf18542005fec0a1002fc605080
  | 8 => 0xf18554006fec0aa0037e6055001beb02a800df18154004f8c0aa002fe65150013f328a800bf99054006fea82a003be5415001beaa0a800ef55054005fcc62a002fd63150017f310a800bf58854005fcc22a002fd61150017f300a800bf58054005fcc9a9803be64d4c015f326a600bf593530077ac9a9802bd64d4c01bfaa6a600df95353006faa9a98037c54d4c017f316a600bf58b53005fcc3a9802fd61d4c017f306a600bf58353006fec9a98037e64d4c019f326a600df59353004fac9a98033d64d4c011eb26a600df19353006fec5a98037e62d4c01beb16a6009f58b53006f8c5a98037f61d4c01bf30ea600df58753004fac3a98037c61d4c01bfb06a600df98353004fcc1a98037d60d4c01be306a600bf59653004facb29802fe6494c017eb24a600dfd5253006faa929802fe6394c01bfa9ca600f7d4e53006bea729802fe6294c017eb14a600bf98653005fac329802fe6094c017eb04a600bfd9153005f8c8a98037f5454c01bf2a2a600df55153006f8a8a9803df5354c01bf29aa600bfd8953005f8c4a9802ff6154c017e30aa600bfd8153005f8c0a98037f6454c013fb22a600df99153006fac8a98037c6454c01bfb1aa600d7d8d53006fec4a98027f6254c01bf312a600df58953006f8c4a98037f6154c013fb0aa600df98553006fac2a98037c6154c01bfb02a600df98153006fac0a98037c6054c013e302a600bf99453004fcca29802fe6414c017eb20a600dfd5053006faa829802fe6314c01bfa98a600f794c53006faa629803dd5314c017f310a600bf58853005fcc229802fd6114c017f300a600bf58053005fecba1802fe65d0c01bf32e86009f99743005facba18037d65d0c013eb2e8600bf19743006fea9a18037d54d0c01bfa9e8600f794f43006faa7a1803dd53d0c01aea9e8600bf98b43005fac5a1802fe61d0c017eb0e8600bf98343005fac1a1802ff6590c017f32c8600df99643004fccb21802fd6590c01beb2c86009f59643005f8cb21802fd6490c01bfaa48600ef95243006faa921803bd5490c019eaa48600bf98e43006fea7218037d5390c01dfa1c8600f7d0e43005fcc521802fd6290c017f30c8600bf58643005fcc121802fd6090c017fb2a8600bf99543006fccaa18027e6550c017eb2a8600df59543004facaa1802fc6550c01bfaa28600df55143006fea6a18037d5350c01efa1a8600ef90d43005fec4a1802fc6250c017fb0a8600bf18543005fec0a1802fc6050c017fb288600bf99443006fcca218027e6510c017eb288600df59443004faca21802fc6510c017f3208600dfd50430077ca8218037d5410c01deaa08600cf55043005fcc6218037f5310c01ef2988600df54c43007baa6218035d5310c01dfa188600f790c430077a8621803dd4310c01cea188600bf98843007dcc4
  | 9 => 0x1800000100800000000100101102500300200400300f01800401500301000400000600800c00d01d00000000902a00000e00200d00000000400100300a01100000600400300000901501500d00400800200c00400000300000000c00700000200b00200d01500300000000200000d00300000500000000000100600000100200000201300500000200200200200100300000100800000900200d00400a00000500000000500000900101100800c00000000c00a00d00000700000401100800f00700000000200000100000100400000100000900000800000700700e00000000600b00200000e00300300300501800000400300b00000100700300b00900000001300501900000200700700800101400e00001c00300000600000200400001600000300000600800000000601c00000100000200700600000000000100000500200500200100000300000500000500f00100601400000800700500000600001601d00000000200500d00700a00000400f00000100000200000200100300900000f01400200001000201200200500000300d04f00000600300300000100000500501200100500100000300900000100100f01900000300100c00000600100002c02700700200b01700300100000001f00c00600001400000001e00000100500200b01700102000300f00500000400500600800500200100100502b00300f00400000000000600102000901300100901a00c00900000f00b00300100200300700400000000800900100200100000100000100f00300000a00002a00100e00b00800400001200000200b00800000e00003000500000000000000000100000000100800700000400e00300000000000100001100b01200800300000e00001900300000100201800100600000d00600100301b00000301300000c00200e003002012001004005fcc7aa003de63d50016f31ea800bf58f54007bac7aa002dd63d50017f316a800bf58b54005fcc3aa002fd61d50017f306a800bf58354006fec7aa0037e63d5001af31ea800df58f54004fac7aa0035d63d50012eb1ea800df18f54006fec5aa0037e62d5001beb16a8009f58b54006f8c5aa0037f61d5001bf30ea800df58754004fac3aa0037c61d5001bfb06a800df98354004fcc1aa0037d60d5001be306a800bf59654004facb2a002fe6495001bfaa4a800efd52540067ea92a002fe63950017eb1ca800bf98a54005fac52a002fe61950017eb0ca800bf98254005fac12a003bf5455001bf2a2a800bfd8d54005f8c6aa002ff62550017e312a800bfd8554005f8c2aa002ff60550017e302a800dfd91540067ec8aa0037f63550013fb1aa800df98d54006fac6aa0037c6355001bfb12a8009fd8954006fcc4aa0037d6255001be312a800dfd8554004fec2aa0037e6155001beb0aa800d
  | 10 => 0xcc0df03a3283114400051e34a00008ba2ac0000000c6600000180006ba7c03f80000f344e32ce09a49b44050cb98d044c0000001ee00ea5b0000063c0000000721a38d3039500010f40000003cc92a02ea3a421610882b856d0bd890836475e06580006c221a0fb800021a41b000000000000022b11fce125ae38208bc000508000000000059f07110fc7ec0b600000000003f300000000000002dc88a48286e700012a80004590e212080001a502e0c2caca000000085c0003a000000000c200037b1678fca7633559ebc8e80002d080000006dc2c900d000018c2ac0000ba600000010f83ba5231db80000000000000000a4800037d1e9400012622e00b87607642d88000afe01b11c02842f470e00016e000047224c82604ee4380001694da60000001f10e1813d19000dc28c6a2161832484857934200707021ab0000598e067d61cf05d892447a02d0238fa45bb000000000006e0001db079200008f80008a80002a300fc8063ef33c05081b668900000000000000928454000000358002c1cc4980001af41943ad33d83dc81e0002da073875e36a0f616140001580001f6c6100173c106fc916000000143426c5ed0a98fa849c2112769b8c7a84290da834c4ac0821c30a3c5820200ad80c885a0001dd80002627c22489b44eb819f0000000cb21c80cc187878a377000091c4727cd0001f2400059d38b8e4499c0002299c5000012e09c80008f80d618c97a42ca2533a300000007fd3d217c8b2024d3f3082c7ca135032812000000022000009142980ab80000004830098d5c03e0242e20bb400000018e95d04320002a41b080000000000000aae44900015d4d8a4f80000ae09703f50061820f8c5e80de00003c433a2e310d02160000bc00006e21dc0001ea400000e1230610c4654540606b4000000157852015c00600100100700000104b00000000101400400300100001400000000000000100100300001c00400202b00100100000200600600000100600100300100000400100000000000000301500b00600f00100500000000200800000c00000100300200600800000000000100400002c01400001500200000800100400000000000000000900000100000200800100500000001401d01100400300000900801200000300900000300400d00a00100100500400100000500100300600001f00600801100100c00300300701700100103b00f00300701a00300100500000100000900100a00000300100002100101f00700300100900000400000200e00900500700000001500100400100100000200000b00100100600700100200100700601900101300900c00700000400000000000000a00101d00200900000600c00500102800400000600500000400000000300b00600000302000700100300002500000000600700000000100
  | 11 => 0x6b500015a00000001749ce8e924970000b740000000db8000000000000000007c1711f6922412c0b912a9000c8800028019bc0006ce000013851220d3fa0c4c04a1ac00000002761233bb026863019c318983c0001ea14586bcd8830d2638000a6804a00000000a64c611610ac4de71e3e380000007a00001f70ea80000001f040000000cf00005900000b70724ca277a1cb952c5fe02c0001ba80d60000001d0000000000000000000002cb07cc3e83d738e8a9c01a1d30002024c6a3123fb146cd505bc0000d0465a39f0000000ce600009917c0a3a000237173c2227e82691d1000000000019588ec0000001d580000e10000000000000000000036208b2b495c40005823c31448f18043022959c00046600000009f60000ed86a89ee7b240007780d257609d065025600127501a8a0400018a135419c6fe0000aec00070600016603c808105417046b238a02492fcc4206f00000000320003fe0f1ce7a0b521e1328e860103dd800000000000000000001a00881e603f00004038a4c000000000000000000000000000005d639f000000000423f000000072b0d80000bba59b34410e83483341ac00003e22c703e1eaccee44c0f791b4e9436e2940968f585e11fe128cf4e37b06413a0d6c3fb1b386144ce07d334036096265c3391bd044875f3d71d2000000000010a09d26762a705441127e10259a0ce3e4c90619374e305c90801ad078c0001980174b0e0352bd01508760000549fc41b44322601c549bc0002ae13445327c33ea99f879c05e3c8842089623e2590bf80000cc2b807e8cc01da1e0889400000013e8e404d0345000117c27856a10a80f491c591000066800040c3451a486ca0000000348d862d31f00e6841227324e941400030532f90805040000001b5000041c0001a5c08c2341b31e402060000360facd2c1930000a68fd67da1491f5c4b201621087c06762870b392d8a2028d0738bc85d875529604f860600016918986b874b0000000000344000023017e7b0251000000061a0eb000014627e15693f4a406273b915402aa6e92e5897400000035d00007880000000000e6c20c00000010020000478000a940000d400000000000d380002fe12122d9a800000310000e740000f904d8000c2c14f00002bc00073f102970c7b434f3d692b0488325099815410a7ed31e90644b82eb05003504e03982131a68caa22d2808c2446c54f0fb04a84ea79622f1b88de651529a9f204502793a282e813c734118141c1544c33608878ab228114a83c490c4a10ae8ce07186290850cdc79e7d83b811187080e530717ac8b4261385133cdfe05f3260e840f072c0581bf439678e2a88ff88d21192ea97909680d92480164f7238f238965483c5783c90f6055000006699c0eb06df1660b440004c82b70f28fc864004a06583ea60b1ec9
  | 12 => 0x14fc00014e0000468c3e7a60468448c08076316121092638d3a09018c9e73115d17a889c0fb00004bca840fa01b0b88ca800000016200000270001c7040200036d0000bdc3622ea0f6c0ac0003281968ca40000000ec40007290001efc0002db0000000c186bc2778c88cbc00000000007c20ef1b6800001044a33500006a24942a614503fa75b0b1000025a0e80048efcc2800003f000066a5373151e74000000000000000062e0001b4800026d17399d0a3015a3bf000045414a3b59c584e200016803c8000000071a048f44000139029cdae32e3898de000077d0c51b58dee0ea3f70000d0c7ff3651b945f010607718c800000000009600006a12a698e0a7464a1f3939810c3ee06a8664a3e21317412b849056f1fc0f301802cf26f85f4ffc0002aa93cc3a82e400000000005033098ef40000002c7800000000021981dc29a74e0000000a2c1612eb80002022aa00000002fc735026895cbb62d731200a44444733708d0c86212718f80000003ab0ac80000001921f219e80001950000ef854832c3240f08f3e321031906893800000000000000000000000c3a210282127cbfc5a613e1dbca8053d40682b47ee2e03228f54b84000000015c0002df25687fc76a3361a3118834c0143b10318dbc6bf04e888cec20fc0001e248204092ee0ff40005af0e80c380cc21b1b91bd4b7414517b05a8f6219b05907148c612834e0fc475037909f80e8c725992229ed4d0e3b837786e04786531d70f7c48a7e734f1ed02186c800005b0a146f2275878c18e71a31d9504f386ac3e51340ab60952d68b3844e2511da03c0d161ae3e60000fc656c0000ba859625400004580002883ae92548d02c50ec89a80e217005f1148c203390001cec00024922b8000db00d719580003223961d491b0ea2757352196ce4255f000000000034a0001814000000119873c0000003c0154cc7c3071361fe09ce7692a913d80001803a1109431050f0af9a08bea34e2170000c126db00c0000ef62ab0001d4cef200000000000004e13648bc4ef07ef000000009802d0001ef89740003941a3ccf244733700e0a443993931180f667bc0610000ee84501530634dd82fc000103800024a299821cf9c00001118947865a0405000000000018b9c08de06e60b78df0b641fb0000c44e1625f00000004387e901185a06c85cd00900000001340001350e3257e21c8b84f3c7950000a1063800012900000006b128c9cb467a4a01051aa408e573348000053e6aa3c78d2c8f621212607a05887a313c0c3000041f19483a40000002c190348c83311db1ab4e6600011901a0a4a2f902780006d00000d19a144c44040000c78ba232a0d10794b6a16d1171ae4000000000087c0000000000000d7c03b00000000000001aa0000fd40000a91f4c000000000000097c50b0c1110cc8e
  | 13 => 0xa8110001d940000000000d1c00000014f000070e00024395f0e100003fd87ac6080000000000af63f21799888000000000027c6845ca26580000001e11f100000005de1b489ac7541471d31444ff27711ce1a6c8d662f3ac80000004f23ad02e0e220002c58ee863400000016b02e800000006a4e000001c000001be0000f30270000000000109ca5210e2991a7c6506a7000046cbbe4652ca0b340000000000000a5c1043b9870ccd6496094933000000031d10580000001ee8b24ad652d0001738bf2000000000000000000011610162070b589040721cd3570708a7661809602dc6b607435b985cfa21d82d49b8054003010314f8b6672a000000098220334980000005660b018800220000be00000000790000a441ea00023516a80e01d23320acc0783760e095840001180000000c9c2852fd88e824024b27e000074e0f80000ee400074706200143f83cb0a80000a421bb08e8000dd04d80898000cba1d72d182f43166813c28e081a03d220a800000064d0000000b081b3049800096e6072849da8b6c4f10000fa45181bd0000bd4c504e439c00006f43ec0c0960056228a13217bc0567943368288f0e6b2367888400072527a1848b4806d3e795887cc57d1b01fd40006d00000e50fee0000001d8064e30f3890000ecc6dd0e51760ba05a23b380002a823b18513889b6000000000000000000017880000000a000006c61140000000ac8000000000000000010a00000000000761cc87e03740488000000000402000036800027c9214d4a4303d5190c20e60113198ac48622030002983425a70491a4452039211e861c23857218013b0b023102210df431240b1ad037872652f183180cdda38e39388100e43bc220800000072300000005aa2e6062939400050c017933400037f262003c32064216a0db069a1023db0bec97600040817e81320000001ef480e66621b1e040001b924d89fc06600039c81e80000642d59268c78124193000040044800e97d0e7847814b14c4cd200000000000000002a20d408c236f0150000000000000000067835e1ab0000f080000c31ee8be60000001da000e2311718dac8fa11e2fe0bd02d255a0001f7800042f000000016263f3e594a8ef851c34a9b00fe45f80bc867500c2dc0df1e207a67fa00318c00883d620b8bdc86a5c814a19f47804442e28d548262501279bb80004f51a9000095658c1d911dc2bc2bd20507e400066131b8fa03981381920d20fe65ec1d612044ca14b1cd800000025b0000000b7a58e0980c6c9b80b42090414f1a2181ef00000b01560000f34a1c80f28b800021e48d0b18ccc4102da29e20205ca5474099d3cc3244f3a9129ca267a10f480007c608a3c58000e400150000e880000000000bbc9a67c500019040005361010df81ec1c0091123041e61c1e880280fe2a51c4
  | 14 => 0x11d4df80260e39668dd64fe3d417f41fc4a61fc9044bca33e1e40cfcb7e3ff24001490062d606e99b0a860000001a6428816416012bc47e4b52ed1818bcc5861071808daa6bb2771c146a652621194680000000e300005f40000001b1c2865272008424d1828e00000001664bc3318000b8000000000000000001a491bc56a0000001e0c0000003669f40e4848f3631db40000022df1db8a925a80528000a6000020e85dc8547df158199cac60cf1b81a749f433236597488100a42549dfc9c022b2611edc0e60dc02883fc1782f03ec8a0c3a206007689b86020803f00a00bc01371fd099804224000003045720000000a6c0000280a48000c2200000000005464b00000000c5a11710b0000e9a0000f394e4e982de0001558db200000008d431c2a9252a00855c2ee0f700003745892269e289e01df00017d84ec0002c99988c6c237021000058c27403d9764e1e7750f012780007ec165115457c47000003acfc43dc00002ac9b25e3033800056e14c00019d4d46173388186cb8e793000135c00053800000007161fe2521abcc2a08813d0b640000000001b902820000001cbc9727dd26b00685680000481a987062600000af101c65807e86d8c9237500000001e821d0688000000671000000000000000000005fa3400001e6cc1404014e800000000025980001766b800001400005e732300000000000000dcc3aa00018b025cc9625e20116280004bd32b810452e32f2db97fc00052b0000188be2680000000000067c00019fc0003b31c482b000000013d8a882e4797233a0146466f10001c6c0002b23468a180000000000078e4477700000009102bf0001acc8300830000e9430658d3971c04aba1f214e19943da7072fb95785844c51e802100002b61a6016cd985cc00013fc00000021b958070a2a12cb8d7c8f200037d9550e6e75018a80001e60e01fa15dcfa83023869be40000000000b60c1
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c100047e7598c100047d7598c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100065e7598c100065d7598c100065f5498c100065d5498c100065e6558c100065d6558c100069e6458c100069d6458c100065e7558c100065d7558c100065f5458c100065d5458c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c100047f76d4c100047d76d4c100053d74d4c100063e64d4c100063d64d4c100065e63d4c100065d63d4c100047f7654c100047d7654c100063e6454c100063d6454c100065e6354c100065d6354c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d88100047e75988100047d7598810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e75988100066d75988100066f54988100066d54988100066f53988100066d53988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066e75588100066d75588100066f54588100066d54588100066f53588100066d5358810006e471588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa70188100047f76d48100047d76d48100063e64d48100063d64d48100065e63d48100065d63d48100066e62d48100066d62d48100057571d48100047f76548100047d76548100063e64548100063d64548100065e63548100065d63548100066e62548100066d62548100057771548100047e75984100047d75984100047d76d44100063e64d44100063d64d44100065e63d44100065d63d44100056d72d44100066e62d44100066d62d44100047f76544100063e64544100063d64544100065e63544100065d63544100066e62544100066d6254410006766154410004f576c84100067565c8410006b564c8410006d563c8410006e562c8410004f57608410006756508410006b56408410006d56308410006e56208410007655208410005f170084100047f76940100047d76940100063e64940100063d64940100065e63940100065d63940100066e62940100066d62940100057571940100047f76140100047d76140100053d74140100063e64140100063d64140100055d73140100065e63140100065d63140100056d72140100066e62140100066d62140100057571140100067565c4010006b564c4010006d563c4010006e562c4010004f97684010006e96284010004f77644010006756544010006b56444010006d56344010005e47244010006e56244010004fb7644010006e96244010
  | 1 => 0x4d100047c7654d100066f65d89100066c65d89100066f75d89100066c75d89100066f54d89100066d54d89100066f53d89100066d53d89100047e75989100047d7598910004ee72989100047f75589100047c7558910004f771589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd7318910004ee76189100066f65189100066c65189100066e75189100066d7518910006ae7418910006ad74189100066f54189100066d5418910006ce7318910006cd73189100066f53189100066d5318910006e57118910006e970189100047e76d49100047c76d49100066f62d49100066c62d49100057571d49100047e76549100047c76549100066f62549100066c62549100047e76d45100056d72d45100066f62d45100066c62d45100057a70d4510005757594510006746594510006e462945100047c76545100066f62545100066c6254510005787054510004f47654510006e46254510006777654510006747654510004747654510005777454510005777354510005777254510007676254510006766254510006746254510007646254510006646254510007737054510005747054510007707054510005757590510005d57390510006e46290510004f47650510005757550510006e4625051000575758c510005b5748c510006e4628c510004f4764c51000575754c510006e4624c510004f67688510005757588510006e46288510007655288510004f47648510005757548510006e462485100047e76941100066f62941100066c62941100047e76141100053d74141100055d73141100056d72141100066f62141100066c6214110005757114110006e86288110007715188110007e22188110004f87648110007695248110007715148110007e121481100077151c4110005777584110006e46284110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d76994100047d74994100047d73994100047d72994100047f74594100047f73594100047f72594100047f71594100047d71594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004f671194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d90100047e75990100047d7599010004bd76990100063e65990100063d65990100063e75990100063d75990100063e65590100063d65590100063e75590100063d75590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047f76d50100047d76d50100063e64d50100063d64d50100055d73d50100047f76550100047d76550100063e64550100063d64550100047e75d8c100047
  | 2 => 0x5777354710005777254710006766254710006746254710005747054710005757590710005d5739071000575755071000575758c710005b5748c71000575754c710005757588710007655288710005757548710006e462487100053d74143100055d73143100056d72143100057571143100047d74d96100047d73d96100047d72d96100067571d96100067a70d9610004be7419610004bd7419610004de7319610004dd7319610004ee7219610004ed72196100053d74196100055d73196100056d72196100063e74196100047d74196100063d74196100043d74196100065e73196100047d73196100065d73196100045d73196100066e72196100047d72196100066d72196100046d72196100067571196100067a70196100047e75992100047d75992100047f75592100047c7559210004df7359210004dc73592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed72192100047e76d52100047c76d52100055d73d52100047e76552100047c76552100063e64552100063d64552100047e7598e100047d7598e100047f7558e100047c7558e10004bf7458e10004bc7458e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e100047e76d4e100047c76d4e100053d74d4e100047e7654e100047c7654e100065e6354e100065d6354e100047e7598a100047d7598a100047f7558a100047c7558a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a100047e76d4a100047c76d4a100057571d4a100047e7654a100047c7654a100066e6254a100066d6254a10005777154a100056d72d46100057a70d46100057870546100067765c8610006776508610006e76208610007655208610005f170086100057571942100053d74142100055d73142100056d7214210005757114210007e02188210007695248210005f07148210007e321482100067765c42100047d74d95100047d73d95100047d72d95100047e7599510004ee7299510004ed7299510004ef7259510004ec72595100047e76195100047d74195100047d73195100047d72195100067571195100047e70195100047c70195100047e75991100047d7599110004ee7299110004ed72991100047f75591100047c7559110004df7359110004dc7359110004ef7259110004ec72591100047e75191100047d75191100047e76d51100047c76d51100055d73d51100057571d51100047e76551100047c76551100047e7598d100047d7598d10004ee7298d10004ed7298d100047f7558d100047c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d100047e7518d100047d7518d100047e76d4d100047c76d4d100053d74d4d100057571d4d100047e765
  | 3 => 0xe64d48200063d64d48200065e63d48200065d63d48200057571d48200047f76548200063e64548200063d64548200065e63548200065d63548200066e62548200047e75984200047d7598420006766598420006756598420006b66498420006b56498420006d66398420006d56398420006767598420006757598420006775498420006755498420006775398420006755398420006775298420006755298420006766558420006756558420006b66458420006b56458420006d66358420006d563584200067675584200067575584200067754584200067554584200067753584200067553584200067752584200067552584200047f76d44200047d76d44200063e64d44200063d64d44200065e63d44200065d63d44200056d72d44200067661d44200067561d44200047f76544200047d76544200063e64544200063d64544200065e63544200065d63544200056f7254420006766154420006756154420004ed76884200066d6588420006ad6488420006cd6388420006e561884200066d6508420006ad6408420006cd6308420006e56108420007655108420005e970084200047f76940200047d76940200063e64940200063d64940200065e63940200065d63940200056d72940200067661940200067561940200047f76140200047d76140200053d74140200063e64140200063d64140200055d73140200065e63140200065d63140200056d72140200057571140200067661140200067561140200066d65c8020006ad64c8020006cd63c8020006e561c8020006f16188020004ef76480200066d6548020006ad6448020006cd6348020005e47148020006e56148020004fb7648020006f16148020004ee7299710004ed72997100056d72997100047d74997100047d73997100066e72997100047d72997100066d72997100046d72997100067671997100047f74597100047f73597100047f72597100047e75d93100047d75d9310004de73d9310004dd73d93100047e75993100047d7599310004ee7299310004ed72993100047e75193100047d75193100047f76d53100047d76d53100055d73d53100057571d53100047f76553100047d76553100047e75d8f100047d75d8f10004be74d8f10004bd74d8f100047e7598f100047d7598f10004ee7298f10004ed7298f100047e7518f100047d7518f100047f76d4f100047d76d4f100053d74d4f100057571d4f100047f7654f100047d7654f100047e75d8b100047d75d8b100047e7598b100047d7598b100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b100047f76d4b100047d76d4b100057571d4b100047f7654b100047d7654b100066f6254b100066c6254b100056d72d4710006766554710005777654710006777654710005777454710
  | 4 => 0x85200067754d85200067554d85200067753d85200067553d85200067752d85200067552d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd73185200066d5218520006776518520006746518520007655218520006767518520006757518520006b67418520006b57418520006775418520006755418520006d67318520006d57318520006775318520006755318520006775218520006e65218520006755218520006e55218520006655218520006e64218520006e54218520006e63218520006e53218520006f170185200047e76d45200047c76d45200056d72d45200067761d45200067461d45200047e76545200047c7654520006776154520006746154520004ee76c85200056d75c8520006e461c85200076551c85200056d7548520006e461485200047e76941200067761941200067461941200047e76141200053d74141200055d73141200056d72141200057571141200067761141200067461141200076952c81200056f7588120006e46188120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d76994200047d74994200047d73994200047d71994200047f74594200047f73594200047f72594200047d72594200047f71594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004ee7219420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d90200047e75990200047d7599020004bd76990200063e65990200063d65990200063e75990200063d75990200063e65590200063d65590200063e75590200063d75590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f571190200047f76d50200047d76d50200063e64d50200063d64d50200055d73d50200047f76550200047d76550200063e64550200063d64550200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c200047e7598c200047d7598c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c200065e7598c200065d7598c200065f5498c200065d5498c200065e6558c200065d6558c200069e6458c200069d6458c200065e7558c200065d7558c200065f5458c200065d5458c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c200047f76d4c200047d76d4c200053d74d4c200063e64d4c200063d64d4c200065e63d4c200065d63d4c200047f7654c200047d7654c200063e6454c200063d6454c200065e6354c200065d6354c200047e75988200047d75988200047d76d48200063
  | 5 => 0x55d73143200056d72143200057571143200047d74d96200047d73d96200066d72d96200047d71d96200067a70d9620004be7419620004bd7419620004de7319620004dd7319620004f67119620004f571196200053d74196200055d73196200057571196200063e74196200047d74196200063d74196200043d74196200065e73196200047d73196200065d73196200045d73196200066d72196200067671196200047d71196200067571196200047571196200067a70196200047e75992200047d75992200047f75592200047c7559220004df7359220004dc73592200047e75192200047d7519220004de7319220004dd7319220004f67119220004f571192200047e76d52200047c76d52200055d73d52200047e76552200047c76552200063e64552200063d64552200047e7598e200047d7598e200047f7558e200047c7558e20004bf7458e20004bc7458e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e200047e76d4e200047c76d4e200053d74d4e200047e7654e200047c7654e200065e6354e200065d6354e200057571d4a200057a70d4a20005787054a200047e75986200047d75986200047f75586200047c75586200047e76d46200056d72d46200047c76546200056f72546200067661546200067561546200066f65886200066f6508620007655108620005e970086200056d72942200053d74142200055d73142200056d72142200057571142200066f65c82200047d74d95200047d73d95200047d71d95200047e7599520004f67199520004f57199520004f77159520004f471595200047e76195200047d74195200047d73195200066d72195200047d71195200047e75991200047d7599120004f67199120004f571991200047f75591200047c7559120004df7359120004dc7359120004f77159120004f471591200047e75191200047d75191200047e76d51200047c76d51200055d73d51200056d72d51200047e76551200047c76551200047e7598d200047d7598d20004f67198d20004f57198d200047f7558d200047c7558d20004bf7458d20004bc7458d20004f77158d20004f47158d200047e7518d200047d7518d200047e76d4d200047c76d4d200053d74d4d200056d72d4d200047e7654d200047c7654d200047e76d49200057571d49200057a70d49200056d75949200066c65949200047c7654920005787054920004ec76549200066f76549200066c76549200046c76549200056f74549200056f73549200056f71549200076b70549200056c70549200076870549200056d7590920005cd7390920004ec76509200056d75509200056d758c920005ad748c920004ec764c9200056d754c9200067765d85200067465d85200076552d85200067775d85200067475d
  | 6 => 0xf53588300066d5358830006cf4358830006cc43588300047f76d48300047d76d48300063e64d48300063d64d48300066e62d48300066d62d48300057571d48300047f76548300047d76548300063e64548300063d64548300066e62548300066d62548300047e75984300047d7598430006766598430006756598430006b66498430006b56498430006e66298430006e56298430006767598430006757598430006775498430006755498430006775398430006755398430006775298430006755298430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006767558430006757558430006775458430006755458430006775358430006755358430006d74358430006d443584300067752584300067552584300047f76d44300047d76d44300063e64d44300063d64d44300056d72d44300066e62d44300066d62d44300067661d44300067561d44300047f76544300047d76544300063e64544300063d64544300066e62544300066d62544300067661544300067561544300047f76940300047d76940300063e64940300063d64940300055d73940300066e62940300066d62940300067661940300067561940300047f76140300047d76140300053d74140300063e64140300063d64140300055d73140300056d72140300066e62140300066d62140300057571140300067661140300067561140300065d65cc0300069d64cc030006cd62cc030006d561cc030006b9648c030004df764c0300065d654c0300059c744c0300069d644c030006cd624c030006d5614c030004fb764c030006b9644c030004f67199720004f571997200057571997200047d74997200047d73997200066e72997200067671997200047d71997200067571997200047571997200047f74597200047f73597200047f71597200047e75d93200047d75d9320004de73d9320004dd73d93200047e75993200047d7599320004f67199320004f571993200047e75193200047d75193200047f76d53200047d76d53200055d73d53200056d72d53200047f76553200047d76553200047e75d8f200047d75d8f20004be74d8f20004bd74d8f200047e7598f200047d7598f20004f67198f20004f57198f200047e7518f200047d7518f200047f76d4f200047d76d4f200053d74d4f200056d72d4f200047f7654f200047d7654f200057571d4b200066e6554b200056f7654b200066f7654b200056f7454b200056f7354b200056f7154b200056c7054b200056d7590b20005cd7390b200056d7550b200056d758cb20005ad748cb200056d754cb200047e75987200047d75987200066d52987200047f76d47200047d76d47200056d72d47200047f76547200047d76547200056d75c87200076551c87200056d75487200053d7414320
  | 7 => 0x4d300055f7454d300071f6454d300065e6454d300065c6454d300071c6454d300061c6454d300055f7254d300055f7154d300075b7054d300055c7054d30007587054d30004de7690d300055d7590d300069c6490d300071d5490d30004dc7650d300055d7550d300069c6450d300047e75189300047d75189300047e76d49300047c76d49300063f64d49300063c64d49300055d73d49300057571d49300047e76549300047c76549300063f64549300063c64549300055d75cc9300069c64cc930005d571cc9300055d754c9300069c644c9300047e75185300047d75185300047e76d45300047c76d45300063f64d45300063c64d45300055d73d45300056d72d45300047e76545300047c76545300063f64545300063c64545300055d75cc5300069c64cc530005cd72cc5300055d754c5300069c644c5300047e76941300063f64941300063c64941300047e76141300053d74141300063f64141300063c64141300055d73141300056d7214130005757114130006b864901300075953901300079a4390130004f876501300073954501300075953501300079943501300075953cc1300055f758c1300069c648c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300047d74994300047d72994300047d71994300047f74594300047f73594300047d73594300047f72594300047f71594300047e7519430004be7419430004bd7419430004de7319430004ee7219430004ed7219430004f67119430004f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d90300047e75990300047d7599030004bd76990300063e65990300063d65990300063e75990300063d75990300063e65590300063d65590300063e75590300063d75590300069c73590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f57119030004fa70190300047f76d50300047d76d50300063e64d50300063d64d50300055d73d50300047f76550300047d76550300063e64550300063d64550300055f73550300047e7598c300047d7598c300047d76d4c300053d74d4c300063e64d4c300063d64d4c300047f7654c300063e6454c300063d6454c300065e6354c30004dd76d0c300065d65d0c300069d64d0c30004dd7610c300065d6510c300069d6410c300071d5410c30005d97010c300047e75988300047d75988300066e65988300066d6598830006ae6498830006ad64988300066e75988300066d75988300066f54988300066d54988300066f53988300066d53988300066e65588300066d6558830006ae6458830006ad64588300066e75588300066d75588300066f54588300066d54588300066
  | 8 => 0x47e75987300047d7598730004be7498730004bd74987300047f76d47300047d76d47300055d73d47300056d72d47300047f76547300047d76547300055d75cc730005cd72cc7300055d754c7300053d74143300055d73143300056d72143300057571143300047d74d96300065d73d96300047d72d96300047d71d96300067a70d9630004be7419630004bd7419630004ee7219630004ed7219630004f67119630004f571196300053d74196300056d72196300057571196300063e74196300047d74196300063d74196300043d74196300065d73196300066e72196300047d72196300066d72196300046d72196300067671196300047d71196300067571196300047571196300067a70196300047e75992300047d75992300047f75592300047c75592300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f571192300047e76d52300047c76d52300055d73d52300047e76552300047c76552300063e64552300063d64552300055f73552300053d74d4e300057a70d4e30005787054e300065f65d0e300065f6510e300069f6410e300071d5410e30005d97010e300047e7598a300047d7598a300047f7558a300047c7558a30004f77158a30004f47158a300047e76d4a300057571d4a300047c7654a300066e6254a300066d6254a300047e75986300047d75986300047f75586300047c7558630004ef7258630004ec72586300047e76d46300056d72d46300047c76546300067661546300067561546300055d73942300053d74142300055d73142300056d7214230005757114230007984390230007395450230005d873502300079b43502300065f65cc2300075a50cc2300075953cc2300047d74d95300047d72d95300047d71d95300047e7599530004be7499530004bd7499530004bf7459530004bc74595300047e76195300047d74195300065d73195300047d72195300047d71195300063f65d91300063c65d91300063f75d91300063c75d91300047e75991300047d7599130004be74991300047f75591300047c7559130004df73591300047e75191300047d7519130004ee7219130004ed7219130004f67119130004f57119130004be76191300063f65191300063c65191300063e75191300063d75191300069d7319130006ae7219130006ad7219130006b67119130006b57119130006b970191300047e76d51300047c76d51300063f64d51300063c64d51300055d73d51300047e76551300047c76551300063f64551300063c64551300047e76d4d300053d74d4d300063f64d4d300063c64d4d300057a70d4d300055d7594d300065c6594d300069c6494d300047c7654d300063f6454d300063c6454d30005787054d30004dc7654d300069c6454d300065f7654d300065c7654d300045c765
  | 9 => 0xd75988400066f54988400066d54988400066f53988400066d53988400066e65588400066d6558840006ce6358840006cd63588400066e75588400066d75588400066f54588400066d54588400066f53588400066d5358840006ae4358840006ac43588400047f76d48400047d76d48400065e63d48400065d63d48400066e62d48400066d62d48400057571d48400047f76548400047d76548400065e63548400065d63548400066e62548400066d62548400047e75984400047d7598440006766598440006756598440006d66398440006d56398440006e66298440006e56298440006767598440006757598440006775498440006755498440006775398440006755398440006775298440006755298440006766558440006756558440006d66358440006d56358440006e66258440006e56258440006767558440006757558440006775458440006755458440006775358440006755358440006b64358440006b443584400067752584400067552584400047f76d44400047d76d44400065e63d44400065d63d44400056d72d44400066e62d44400066d62d44400067661d44400067561d44400047f76544400047d76544400065e63544400065d63544400066e62544400066d62544400067661544400067561544400047f76940400047d76940400053d74940400065e63940400065d63940400066e62940400066d62940400067661940400067561940400047f76140400047d76140400053d74140400055d73140400065e63140400065d63140400056d72140400066e62140400066d62140400057571140400067661140400067561140400063d65d00400069d63d0040006ad62d0040006b561d0040006d96390040004bf76500400063d65500400059c73500400069d6350040006ad6250040006b56150040004fb7650040006d96350040004be7499730004bd74997300053d74997300063e74997300047d74997300063d74997300043d74997300065e73997300047d72997300047d71997300047f74597300047f72597300047f71597300047e75d93300047d75d93300047e75993300047d75993300047e75193300047d7519330004ee7219330004ed7219330004f67119330004f571193300047f76d53300047d76d53300055d73d53300047f76553300047d76553300063f64553300063c64553300053d74d4f300065e6594f300065e6554f300055f7654f300065f7654f300055f7454f300065e6454f300065c6454f300055f7254f300055f7154f300055c7054f300055d7590f300071d5490f300055d7550f300069c6450f300047e7598b300047d7598b30004be7498b30004bd7498b300047f76d4b300047d76d4b300055d73d4b300057571d4b300047f7654b300047d7654b300055d75ccb30005d571ccb300055d754cb30
  | 10 => 0x51400047c7655140005787055140004bc76551400063f76551400063c76551400043c76551400053f73551400053f72551400053f71551400073b70551400053c70551400073870551400065f65d8d400065c65d8d400071d54d8d400065f75d8d400065c75d8d400065f54d8d400065d54d8d400047e7518d400047d7518d400063d5418d40004ee7218d40004ed7218d40004f67118d40004f57118d400065f6518d400065c6518d400071d5418d400065e7518d400065d7518d400065f5418d400069e5418d400065d5418d400069d5418d400061d5418d40006ce7218d40006cd7218d40006d67118d40006d57118d40006d97018d400047e76d4d400047c76d4d400053d74d4d400065f63d4d400065c63d4d400047e7654d400047c7654d400065f6354d400065c6354d40004be76d0d400053d75d0d400069c63d0d400071d53d0d400053d7550d400069c6350d400047e75189400047d75189400047e76d49400047c76d49400053d74d49400065f63d49400065c63d49400057571d49400047e76549400047c76549400065f63549400065c63549400053d75d09400069c63d0940005b571d09400053d75509400069c63509400047e75185400047d75185400047e76d45400047c76d45400053d74d45400065f63d45400065c63d45400056d72d45400047e76545400047c76545400065f63545400065c63545400053d75d05400069c63d0540005ad72d05400053d75505400069c63505400047e76941400065f63941400065c63941400047e76141400053d74141400055d73141400065f63141400065c63141400056d72141400057571141400073954d01400053f75901400069c6390140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d76994400047d73994400047d72994400047d71994400047f74594400047d74594400047f73594400047f72594400047f71594400047e7519440004be7419440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f571194400047e75990400047d75990400047d76d50400055d73d50400047f76550400063e64550400047e7598c400047d7598c400065e6598c400065d6598c400065e7598c400065d7598c400065f5498c400065d5498c400065e6558c400065d6558c400065e7558c400065d7558c400065f5458c400065d5458c400047f76d4c400047d76d4c400053d74d4c400065e63d4c400065d63d4c400047f7654c400047d7654c400053f7454c400065e6354c400065d6354c40004bd7690c400063d6590c400069d6390c400063d6510c400069d6310c400071d5310c40005b97010c400047e75988400047d75988400066e65988400066d6598840006ce6398840006cd63988400066e75988400066
  | 11 => 0x65e63980500065d63980500066e62980500066d62980500067661980500067561980500067a70980500073a64980500073964980500075a63980500075963980500076a6298050007696298050007726198050007716198050004de7399740004dd73997400055d73997400063e74997400065e73997400047d73997400065d73997400045d73997400047d72997400047d71997400047f73597400047f72597400047f71597400055d73d53400063e65953400063e65553400053f76553400063f76553400053f73553400053f72553400053f71553400053c70553400047e7598f400047d7598f400063d5498f400047f76d4f400047d76d4f400053d74d4f400047f7654f400047d7654f400053d75d0f400071d53d0f400053d7550f400047e7598b400047d7598b40004de7398b40004dd7398b400047f76d4b400047d76d4b400053d74d4b400057571d4b400047f7654b400047d7654b400053d75d0b40005b571d0b400053d7550b400047e75987400047d7598740004de7398740004dd73987400047f76d47400047d76d47400053d74d47400056d72d47400047f76547400047d76547400053d75d0740005ad72d07400053d75507400053d74143400055d73143400056d72143400057571143400063d74d96400047d73d96400047d72d96400047d71d96400067a70d9640004de7319640004dd7319640004ee7219640004ed7219640004f67119640004f571196400055d73196400056d72196400057571196400063d74196400065e73196400047d73196400065d73196400045d73196400066e72196400047d72196400066d72196400046d72196400067671196400047d71196400067571196400047571196400067a70196400055d73d52400057a70d52400057870552400047e7598e400047d7598e400047f7558e400047c7558e400047e76d4e400053d74d4e400047c7654e400053f7454e400065e6354e400065d6354e400063f6590e400063f6510e400071d5310e40005b97010e400047e7598a400047d7598a400047f7558a400047c7558a40004f77158a40004f47158a400047e76d4a400057571d4a400047c7654a400066e6254a400066d6254a400047e75986400047d75986400047f75586400047c7558640004ef7258640004ec72586400047e76d46400056d72d46400047c76546400067661546400067561546400053d74942400053d74142400055d73142400056d72142400057571142400063f65d02400073a50d02400073954d02400047d73d95400047d72d95400047d71d95400047e7599540004de7399540004dd7399540004df7359540004dc73595400047e76195400063d74195400047d73195400047d72195400047d71195400047e76d51400055d73d51400057a70d51400053d75951400063c659
  | 12 => 0x564984500073564984500063564984500067763984500075663984500067563984500075563984500065563984500067762984500076662984500067562984500076562984500066562984500063e64584500063d64584500065e63584500065d63584500066e62584500066d62584500047f74584500047f73584500047f72584500067776584500067764584500067664584500073664584500063664584500067564584500073564584500063564584500067464584500067763584500067663584500075663584500065663584500067563584500075563584500065563584500067463584500067762584500067662584500076662584500066662584500067562584500076562584500066562584500067462584500067774584500067674584500067574584500067474584500067773584500067673584500067573584500067473584500067743584500067643584500067543584500067443584500067772584500067672584500067572584500067472584500067742584500067642584500067542584500067442584500067732584500067632584500067532584500067432584500067670584500067470584500053e74184500053d74184500063d64184500055e73184500055d73184500065d63184500056e72184500056d72184500066d62184500057671184500067561184500057a70184500047e76d04500047d76d04500063d64d04500065d63d04500056e72d04500056d72d04500066d62d04500067561d04500047e76904500047d76904500063d64904500055e73904500055d73904500065d63904500066d62904500067561904500047d76504500063d64504500065d63504500066d62504500067561504500047e76104500047d76104500063d64104500065d63104500066d62104500067561104500047e76cc4500047d76cc4500063d64cc4500065d63cc4500056e72cc4500056d72cc4500066d62cc4500067561cc4500047e768c4500047d768c4500053e748c4500053d748c4500063d648c4500065d638c4500066d628c45000675618c4500047d764c4500063d644c4500065d634c4500066d624c45000675614c4500047e760c4500047d760c4500063d640c4500065d630c4500066d620c45000675610c4500047e76c84500047d76c84500063d64c84500065d63c84500066d62c84500067561c84500047e76884500047d76884500063d64884500065d63884500066d62884500067561884500047d76484500063d64484500065d63484500066d62484500067561484500047e76084500047d76084500053e74084500053d74084500063d64084500055e73084500055d73084500065d63084500066d62084500067561084500076521084500057a70084500057970084500063e64980500063d6498050
  | 13 => 0x8c500065d6318c500056e7218c500056d7218c50005767118c50005757118c500057a7018c500047e76d0c500047d76d0c500063d64d0c500065d63d0c500047e7690c500047d7690c500063d6490c500065d6390c500047d7650c500063d6450c500065d6350c500047e7610c500047d7610c500063d6410c500065d6310c500071d4310c500056e7210c500056d7210c50005767110c50005757110c500057a7010c50005797010c500053e74d88500053d74d88500063e64d88500063d64d88500055e73d88500055d73d88500065e63d88500065d63d88500057671d88500057571d88500057a70d88500063d64988500065d63988500056d76988500066f64988500072e64988500066d64988500072d64988500062d64988500066f63988500074e63988500066d63988500074d63988500064d63988500063e64588500063d64588500065e63588500065d63588500047f74588500047f73588500047f71588500066f76588500066f64588500066e64588500072e64588500062e64588500066d64588500072d64588500062d64588500066c64588500066f63588500066e63588500074e63588500064e63588500066d63588500074d63588500064d63588500066c63588500066f74588500066e74588500066d74588500066c74588500066f73588500066e73588500066d73588500066c73588500066f43588500066e43588500066d43588500066c43588500066f71588500066e71588500066d71588500066c71588500066e70588500066c70588500053e74188500053d74188500063d64188500055e73188500055d73188500065d63188500056e72188500066d62188500057671188500057571188500057a70188500047e76d08500047d76d08500063d64d08500065d63d08500066d62d08500057671d08500057571d08500047e76908500047d76908500063d64908500055e73908500055d73908500065d63908500066d62908500047d76508500063d64508500065d63508500066d62508500047e76108500047d76108500063d64108500065d63108500066d62108500047e76cc8500047d76cc8500063d64cc8500065d63cc8500066d62cc8500057671cc8500057571cc8500047e768c8500047d768c8500053e748c8500053d748c8500063d648c8500065d638c8500066d628c8500047d764c8500063d644c8500065d634c8500066d624c8500047e760c8500047d760c8500063d640c8500065d630c8500066d620c8500053e74d84500053d74d84500063e64d84500063d64d84500055e73d84500055d73d84500065e63d84500065d63d84500056e72d84500056d72d84500066e62d84500066d62d84500057a70d84500063d64984500065d63984500066d62984500057576984500067764984500073664984500067
  | 14 => 0x66c53588500063e64d48500063d64d48500065e63d48500065d63d48500066d62d48500057671d48500057571d48500047d76948500063d64948500065d63948500066d62948500063e64548500063d64548500065e63548500065d63548500066e62548500063d64148500065d63148500066d6214850006b66498450006b56498450006d66398450006d56398450006e66298450006e56298450006775498450006755498450006775398450006755398450006775298450006755298450006b66458450006b56458450006d66358450006d56358450006e66258450006e562584500067675584500067754584500067654584500067554584500067454584500067753584500067653584500067553584500067453584500067752584500067652584500067552584500067452584500063e64d44500063d64d44500065e63d44500065d63d44500056e72d44500056d72d44500066e62d44500066d62d44500067561d44500047d76944500063d64944500065d63944500066d62944500067561944500063e64544500063d64544500065e63544500065d63544500066e62544500066d62544500067661544500063d64144500065d63144500066d62144500067561144500063d64d40500065d63d40500066d62d40500067561d40500047f76540500063d64540500065d63540500066d6254050006756154050004fb76540500055e73d90500055d73d90500056e72d90500056d72d90500057671d90500057571d90500057a70d90500063f64990500053d76990500047f73590500047f72590500047f71590500063f76590500063f73590500063e73590500063d73590500063c73590500063f72590500063e72590500063d72590500063c72590500063f71590500063e71590500063d71590500063c71590500063e70590500063c70590500053e74190500063d64190500055e73190500055d73190500056e72190500056d72190500057671190500057571190500057a70190500053e74d8c500053d74d8c500063e64d8c500063d64d8c500056e72d8c500056d72d8c500057671d8c500057571d8c500057a70d8c500063d6498c500065f6398c500055d7698c500065f6498c500071e6498c500065d6498c500071d6498c500061d6498c500063e6458c500063d6458c500047f7458c500047f7258c500047f7158c500065f7658c500065f6458c500065e6458c500071e6458c500061e6458c500065d6458c500071d6458c500061d6458c500065c6458c500065f7458c500065e7458c500065d7458c500065c7458c500065f7258c500065e7258c500065d7258c500065c7258c500065f7158c500065e7158c500065d7158c500065c7158c500065e7058c500065c7058c500053e7418c500053d7418c500063d6418c500055e731
  | 15 => 0x77158a50004777158a50006747158a500053e7418a500053d7418a500055e7318a500055d7318a50005767118a50005757118a500057a7018a500047e76d0a500047d76d0a500063d64d0a500057671d0a500057571d0a500047e7690a500047d7690a500055e7390a500055d7390a500066d6290a500047d7650a500063d6450a500066d6250a500047e7610a500047d7610a500047e76cca500047d76cca500065d63cca500057671cca500057571cca500047e768ca500047d768ca500053e748ca500053d748ca500066d628ca500047d764ca500065d634ca500066d624ca500047e760ca500047d760ca500057a70d86500067761986500056f72586500056c72586500047f74586500047f73586500047f72586500066f72586500046f72586500066c72586500053e74186500053d74186500055e73186500055d73186500056e72186500056d72186500057a70186500047e76d06500047d76d06500063d64d06500056e72d06500056d72d06500047e76906500047d76906500055e73906500055d73906500067561906500047d76506500063d64506500067561506500047e76106500047d76106500047e76cc6500047d76cc6500065d63cc6500056e72cc6500056d72cc6500047e768c6500047d768c6500053e748c6500053d748c65000675618c6500047d764c6500065d634c65000675614c6500047e760c6500047d760c6500047e76c86500047d76c86500066d62c86500047e76886500047d76886500067561886500047d76486500066d62486500067561486500047e76086500047d76086500053e74086500053d74086500055e73086500055d73086500076521086500057a70086500057970086500047e76d51500055d73d51500063f64551500047e76d4d500053d74d4d500065f6354d500047e76d49500057571d49500066f62549500047e76d45500056d72d45500067761545500063e75590500063e64d50500063d64d50500055e73d50500055d73d50500047d76950500063d64950500063e64550500063d64150500069e6498c500069d6498c500065f5498c500065d5498c500069e6458c500069d6458c500065e7558c500065f5458c500065e5458c500065d5458c500065c5458c500053e74d4c500053d74d4c500063e64d4c500063d64d4c500065e63d4c500065d63d4c500047d7694c500063d6494c500065d6394c500063e6454c500063d6454c500065e6354c500063d6414c500065d6314c50006ae6498850006ad6498850006ce6398850006cd63988500066f54988500066d54988500066f53988500066d5398850006ae6458850006ad6458850006ce6358850006cd63588500066e75588500066f54588500066e54588500066d54588500066c54588500066f53588500066e53588500066d5358850
  | 16 => 0x8421007675448421007655448421005e77348421005e57348421007c66348421007c56348421007675348421007655348421005e470484210067a6598021006796598021006ba6498021006b96498021006da6398021006d96398021007695298021007715198021007e121980210067b75980210067875980210067b54980210067954980210067b53980210067953980210067b52980210067952980210067b51980210067951980210047f75580210047c75580210066d5258021006755158021006e521580210067a6558021006796558021006ba6458021006b96458021006da6358021006d96358021007695258021007715158021007e121580210067b75580210067875580210067b54580210067954580210067b53580210067953580210067b5258021006ea5258021006795258021006e95258021006695258021006ea4258021006e94258021006ea3258021006e932580210067b5158021006f25158021006795158021006f15158021006715158021006f24158021006f14158021006f23158021006f13158021006eb2158021006f22158021006e92158021006f12158021006e121580210063e64d53500063d64d53500055d73d53500053d74d4f500065e63d4f500065d63d4f500066d62d4b500057571d4b500056d72d47500067561d4750004df7359250004dc73592500055e73d52500055d73d52500063d64952500057970952500063e64552500063d6455250004bf7458e50004bc7458e500053e74d4e500053d74d4e500065d6394e50005797094e500065e6354e500065d6354e50004f77158a50004f47158a500057671d4a500057571d4a500066e6254a500066d6254a50004ef7258650004ec72586500056e72d46500056d72d46500067661546500067561546500057a70d92500063f64992500055f73592500055c73592500047f73592500065f73592500045f73592500065c73592500047f72592500047f71592500063d64192500055e73192500055d73192500056e72192500056d72192500057671192500057571192500057a70192500057a70d8e500065f6398e500053f7458e500053c7458e500047f7458e500063f7458e500043f7458e500063c7458e500047f7258e500047f7158e500053e7418e500053d7418e500065d6318e500056e7218e500056d7218e50005767118e50005757118e500057a7018e500047e76d0e500047d76d0e500063d64d0e500047e7690e500047d7690e500065d6390e500047d7650e500063d6450e500065d6350e500047e7610e500047d7610e500071d4310e500056e7210e500056d7210e50005767110e50005757110e500057a7010e50005797010e500057a70d8a500066f6298a50005777158a50005747158a500047f7458a500047f7358a500047f7158a500067
  | 17 => 0x65e6598c210065d6598c210069e6498c210069d6498c210065e7598c210065d7598c210065f5498c210065d5498c21006ce7298c21006d67198c210065e6558c210065d6558c210069e6458c210069d6458c210065e7558c210065d7558c210065f5458c210065d5458c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004fa7018c21004f97018c210047f76d4c210047d76d4c210053d74d4c210063e64d4c210063d64d4c210065e63d4c210065d63d4c210056d72d4c210057571d4c210047f7654c210047d7654c210063e6454c210063d6454c210065e6354c210065d6354c210047e75988210047d75988210047d76d48210063e64d48210063d64d48210065e63d48210065d63d48210057571d4821004ed76948210056d7594821005e571948210047f76548210063e64548210063d64548210065e63548210065d63548210066e65548210056f76548210066f76548210056f74548210072e64548210072d64548210056f73548210074e63548210074d63548210056f71548210076671548210076571548210056c7054821004ed76908210056d7590821005cd7390821006cd6390821005e571908210056d7550821006ae6450821006cd6350821004ed768c8210056d758c821005ad748c821006ad648c821005e5718c8210056d754c821006ad644c821006ce634c8210047e75984210047d75984210066d52984210047d76d44210063e64d44210063d64d44210065e63d44210065d63d44210056d72d4421004f57694421005757594421005e572944210076552944210047f76544210063e64544210063d64544210065e63544210065d6354421006766554421007665254421007655254421005777654421006777654421005777454421007366454421007356454421005777354421007566354421007556354421005777254421007667254421007657254421006766254421007664254421007654254421007663254421007653254421005747054421004f57690421005757590421005d57390421006d56390421005e57290421007655290421005757550421006b66450421006d56350421007655250421007a54250421004f5768c42100575758c421005b5748c421006b5648c421005e5728c42100765528c42100575754c421006b5644c421006d6634c42100765524c421007c5324c4210056d75c84210076551c8421005757588421005e57288421007655288421004ef76484210056d7548421007675148421007655148421004f77648421005757548421007675248421007655248421005e77648421006e77648421005e77548421007667548421005e57548421007657548421005657548421007666548421007656548421005e77448421005e57448421007a66448421007a5644
  | 18 => 0xf76552210047d76552210047e75d8e210047d75d8e21004be74d8e21004bd74d8e210047e7598e210047d7598e210047e7518e210047d7518e210047f76d4e210047d76d4e210053d74d4e210056d72d4e210047f7654e210047d7654e210057571d4a210066e6594a21005777154a210066f7654a210066c7654a210056f7454a210056f7354a210056f7154a21007677154a21007647154a210056c7054a210056d7590a21005cd7390a210056d7550a210056d758ca21005ad748ca210056d754ca210056d72d46210056d75c86210067565c86210047f75582210047c75582210066d5258221004ed7299521004f571995210047d74995210047d73995210047d72995210066d72995210046d72995210047d71995210067571995210047571995210047e70995210047f74595210047f73595210047f72595210066f72595210047f71595210067771595210047c70595210047e75d91210047d75d9121004de73d9121004dd73d91210047e75991210047d7599121004ed7299121004f571991210047e75191210047d75191210047f76d51210047d76d51210055d73d51210047f76551210047d76551210047e75d8d210047d75d8d21004be74d8d21004bd74d8d210047e7598d210047d7598d21004ed7298d21004f57198d210047e7518d210047d7518d210047f76d4d210047d76d4d210053d74d4d210047f7654d210047d7654d210057571d49210057771549210056d72d45210047f76545210047d76545210056f72545210067565c85210066d65885210047e75d81210047d75d81210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d76994210047d74994210047d73994210066e72994210067671994210047e70994210047f74594210047f73594210047c70594210047e7519421004be7419421004bd7419421004de7319421004dd7319421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d90210047e75990210047d7599021004bd76990210063e65990210063d65990210063e75990210063d7599021006ae7299021006b671990210063e65590210063d65590210063e75590210063d75590210047e75190210047d7519021004be7419021004de7319021004dd7319021004fa7019021004f970190210047f76d50210047d76d50210063e64d50210063d64d50210055d73d50210056d72d50210057571d50210047f76550210047d76550210063e64550210063d64550210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c210047e7598c210047d7598c21004dd7698c21
  | 19 => 0x51310047d76d51310055d73d51310047f76551310047d76551310063f64551310063c64551310055f73551310053d74d4d310057571d4d31005777154d31004de76d0d310065d65d0d310065d6510d310069d6410d310071d5410d31005cd7210d31005d67110d31005d97010d310047e75d89310047d75d89310047e75189310047d75189310047d76d49310057571d49310047f76549310066f62549310066c6254931005777154931005d671cc9310055d73d45310056d72d45310047f76545310047d76545310055f7354531005d67390531004f47650531007944350531005e672cc5310059e748c5310047e75d81310047d75d81310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed72181310047d76994310047d74994310047d72994310047e70994310047f74594310047f72594310047c70594310047e75194310047e75d90310047d75d9031004de73d90310047e75990310047d75990310047e75190310047d7519031004ee7219031004ed7219031004f67119031004fa7019031004f970190310047f76d50310047d76d50310055d73d50310047f76550310047d76550310047e7598c310047d7598c310047d76d4c310053d74d4c310047f7654c310047e75988310047d75988310047f76d48310047d76d48310057571d48310047f76548310047d76548310047e75984310047d7598431004be7498431004bd74984310047d76d44310056d72d44310047f7654431004df764c431004f7764c4310047f75580310047c75580310047d74997210047d73997210067571997210047e70997210047f74597210047f73597210047c70597210047e75d93210047d75d9321004de73d9321004dd73d93210047e75993210047d75993210047e75193210047d75193210047f76d53210047d76d53210055d73d53210057571d53210047f76553210047d76553210047e75d8f210047d75d8f21004be74d8f21004bd74d8f210047e7598f210047d7598f210047e7518f210047d7518f210047f76d4f210047d76d4f210053d74d4f210057571d4f210047f7654f210047d7654f210056d72d47210067665947210056f7254721005777654721006777654721006747654721005777454721005777354721005777254721007677254721007647254721005747054721005757590721005d5739072100575755072100575758c721005b5748c72100575754c7210047f75583210047c75583210067551583210047d74996210047d73996210066d72996210047e70996210047f74596210047f73596210047c70596210047e75d92210047d75d9221004de73d9221004dd73d92210047e75992210047d75992210047e75192210047d75192210047f76d52210047d76d52210055d73d52210056d72d52210047
  | 20 => 0x47d75d9331004ee72d9331004ed72d93310047e75993310047d75993310047e75193310047d7519331004ee7219331004ed7219331004fa7019331004f970193310047f76d53310047d76d53310055d73d53310047f76553310047d76553310055f73553310053d74d4f310065d65d0f310065d6510f310069d6410f310071d5410f31005cd7210f31005d97010f310047e7598b310047d7598b31004be7498b31004bd7498b310066e6598b310066d6598b310066e7598b310066d7598b31006ae7498b31006ad7498b310066f5498b310066d5498b310066f5398b310066d5398b310066e6558b310066d6558b310066e7558b310066d7558b310066f5458b310066d5458b310066f5358b310066d5358b31006cf4358b31006cc4358b310047f76d4b310047d76d4b310066e62d4b310066d62d4b310057571d4b310047f7654b310047d7654b310066e6254b310066d6254b31006ce624cb310055d73d47310056d72d47310066e62d47310066d62d47310055f73547310066e62547310066d62547310047f75583310047c7558331004be74d9631004bd74d96310047d74996310047d72996310047e70996310047f74596310047f72596310047c7059631004be7419631004bd74196310047e75d92310047d75d92310047e75992310047d7599231004ee7299231004ed72992310063e65992310063d65992310063e75992310063d7599231006ae7299231006ad7299231006b671992310063e65592310063d65592310063e75592310063d75592310047e75192310047d75192310047f76d52310047d76d52310063e64d52310063d64d52310055d73d52310047f76552310047d76552310063e64552310063d64552310053d74d4e310063e64d4e310063d64d4e310057571d4e310063e6454e310063d6454e31005777154e310047e7598a310047d7598a310047f76d4a310047d76d4a310063e64d4a310063d64d4a310057571d4a310047f7654a310047d7654a310063e6454a310063d6454a31005777154a310063e64d46310063d64d46310056d72d46310063e64546310063d6454631006b664506310069e64cc6310075551cc6310075553cc631005e672cc6310047f75582310047c7558231004be7499531004bd7499531004ee7299531004ed72995310053d74995310056d72995310063e74995310047d74995310063d74995310043d74995310047d73995310065d73995310066e72995310047d72995310066d72995310046d72995310047d71995310067571995310047e70995310047f74595310047f73595310065f73595310047f72595310047f71595310067771595310047c70595310047e75d91310047d75d91310047e75991310047d7599131004ee7299131004ed72991310047e75191310047d75191310047f76d
  | 21 => 0x571d52410057771552410047e7598e410047d7598e41004ee7298e41004ed7298e410065e6598e410065d6598e410065e7598e410065d7598e410065f5498e410065d5498e41006ce7298e41006cd7298e41006d67198e410065e6558e410065d6558e410065e7558e410065d7558e410065f5458e410065d5458e410047f76d4e410047d76d4e410053d74d4e410065e63d4e410065d63d4e410047f7654e410047d7654e410065e6354e410065d6354e410047e7598a410047d7598a410047f76d4a410047d76d4a410065e63d4a410065d63d4a410057571d4a410047f7654a410047d7654a410065e6354a410065d6354a41005777154a410065e63d46410065d63d46410056d72d46410065e63546410065d63546410069e63d06410073551d06410073554d0641005e672d06410047f75582410047c7558241004de7399541004dd7399541004ee7299541004ed72995410055d73995410056d72995410047d74995410063d74995410065e73995410047d73995410065d73995410045d73995410066e72995410047d72995410066d72995410046d72995410047d71995410067571995410047e70995410047f74595410063f74595410047f73595410047f72595410047f71595410067771595410047c70595410055d73d51410057571d51410057771551410047e75d8d410047d75d8d410047e7518d410047d7518d410047d76d4d410053d74d4d410047f7654d410053f7454d410065f6354d410065c6354d410063d6590d410063d6510d410071d5310d41005ad7210d41005b67110d41005b97010d410047e75d89410047d75d89410047e75189410047d75189410047d76d49410057571d49410047f76549410066f62549410066c6254941005777154941005b671d09410053d74d45410056d72d45410047f76545410047d76545410053f7454541005e672d05410059e73905410047e75d81410047d75d81410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed72181410047d76994410047d73994410047d72994410047e70994410047f73594410047f72594410047c70594410047e75194410047e75990410047d75990410047d76d50410055d73d50410047f76550410047e7598c410047d7598c410047f76d4c410047d76d4c410053d74d4c410047f7654c410047d7654c410047e75988410047d75988410047f76d48410047d76d48410057571d48410047f76548410047d76548410047e75984410047d75984410047d76d44410056d72d44410047f7654441004bf7650441004f776504410047f75580410047c7558041004ee72d9731004ed72d97310047d74997310047d72997310047e70997310047f74597310047f72597310047c7059731004ee7219731004ed72197310047e75d9331
  | 22 => 0xd510047e7650d510047e7610d510047d7610d510071d4310d510056e7210d510056d7210d51005767110d51005757110d510057a7010d51005797010d510047d74d89510047d73d89510067571d89510047e70d89510057571989510057771589510066d62189510047e76d09510047d76d09510057671d09510057571d09510047e76909510047d76909510055e73909510055d73909510066f62909510047e76509510066f62509510057771509510057471509510047e76109510047d76109510047e76cc9510047d76cc9510057671cc9510057571cc9510047e768c9510047d768c9510053e748c9510053d748c9510066f628c9510047e764c9510066f624c95100577714c95100574714c9510047e760c9510047d760c9510056e72d85510056d72d85510057672d85510076672d85510056672d85510076572d85510057570d85510056f72581510056c72581510053e74181510053d74181510055e73181510055d73181510056e72181510056d72181510063e74181510047d74181510063d74181510043d74181510065e73181510047d73181510065d73181510045d73181510066e72181510047d72181510066d72181510046d72181510066e72994510066d72994510063e64d50510063d64d50510055d73d50510047f76550510053d74d4c510065e63d4c510065d63d4c510047f7654c510066d62d48510057571d48510047f76548510056d72d44510047f7654451004f77654451006766554451004ee72d9741004ed72d97410047d73997410047d72997410047e70997410047f73597410047f72597410047c7059741004ee7219741004ed72197410055d73d53410047e7598f410047d7598f410047f76d4f410047d76d4f410053d74d4f410047f7654f410047d7654f410053f7454f410063d6590f410063d6510f410069d6310f410071d5310f41005ad7210f41005b97010f410047e7598b410047d7598b41004de7398b41004dd7398b410066e6598b410066d6598b410066e7598b410066d7598b410066f5498b410066d5498b41006ce7398b41006cd7398b410066f5398b410066d5398b410066e6558b410066d6558b410066e7558b410066d7558b410066f5458b410066d5458b410066f5358b410066d5358b41006ae4358b41006ac4358b410047f76d4b410047d76d4b410066e62d4b410066d62d4b410057571d4b410047f7654b410047d7654b410066e6254b410066d6254b41006ae6250b410053d74d47410056d72d47410066e62d47410066d62d47410053f74547410066e62547410066d62547410047f75583410047c7558341004de73d9641004dd73d96410047d73996410047d72996410047e70996410047f73596410047f72596410047c7059641004de7319641004dd73196410055d73d52410057
  | 23 => 0x47f7258f510047c7058f510056e7218f510056d7218f51005757118f510047e76d0f510047d76d0f510065d63d0f510047e7690f510047d7690f510063d6490f510047d7650f510047e7610f510047d7610f510063d6410f510065d6310f510071d4310f510056e7210f510056d7210f51005767110f51005757110f510057a7010f51005797010f510057571d8b510066f6498b510066d6498b510066f6398b510066d6398b510047f7458b510047f7358b510047c7058b510066f7658b510066f6458b510066e6458b510066d6458b510066c6458b510066f6358b510066e6358b510066d6358b510066c6358b510066f7458b510066e7458b510066d7458b510066c7458b510066f7358b510066e7358b510066d7358b510066c7358b510066f4358b510066e4358b510066d4358b510066c4358b510066f7158b510066d7158b510066f7058b510066e7058b510066d7058b510066c7058b510066d6218b51005757118b510047e76d0b510047d76d0b510066d62d0b510057671d0b510057571d0b510047e7690b510047d7690b510055e7390b510055d7390b510066d6290b510047d7650b510066d6250b510047e7610b510047d7610b510066d6210b510047e76ccb510047d76ccb510066d62ccb510057671ccb510057571ccb510047e768cb510047d768cb510053e748cb510053d748cb510066d628cb510047d764cb510066d624cb510047e760cb510047d760cb510066d620cb510056e72d83510056d72d83510066d62d83510066e62983510066d62983510047d74983510047d73983510047d72983510066d62583510053e74183510053d74183510055e73183510055d73183510056e72183510056d72183510066e62183510066d62183510055d73d52510063d64552510053d74d4e510065d6354e510057571d4a510066d6254a510056d72d4651005e672d4651004de73d9151004dd73d91510055e73d51510055d73d51510063f64951510063f64551510047e7615151004be74d8d51004bd74d8d510053e74d4d510053d74d4d510065f6394d510065f6354d510047e7614d510057671d49510066f62549510066c62549510057471549510047e7614951005e672d4551004be7418151004bd7418151004de7318151004dd7318151004ee7218151004ed72181510055e73d91510055d73d91510065e73d91510047d73d91510065d73d91510045d73d91510047d72d91510047e70d91510063f64991510056e72991510056d72991510057571991510057771591510053e74d8d510053d74d8d510063e74d8d510047d74d8d510063d74d8d510043d74d8d510047d72d8d510047e70d8d510065f6398d510056e7298d510056d7298d51005757198d51005777158d510047e76d0d510047d76d0d510047e7690d510047d769
  | 24 => 0xd52cca320074d53cca32005e671cca320047e75986320047d75986320047f75582320047c7558232004be7499532004bd7499532004f67199532004f571995320053d74995320057571995320063e74995320047d74995320063d74995320043d74995320047d73995320065d73995320047d72995320066d72995320067671995320047d71995320067571995320047571995320047e70995320047f74595320047f73595320065f73595320047f72595320066f72595320047f71595320047c70595320047e75d91320047d75d91320047e75991320047d7599132004f67199132004f571991320047e75191320047d75191320047f76d51320047d76d51320055d73d51320047f76551320047d76551320063f64551320063c64551320055f73551320053d74d4d320056d72d4d320056f7254d32004de76d0d320065d65d0d320065d6510d320069d6410d320071d5410d32005ce7210d32005d57110d32005d97010d320055d73d49320057571d49320047f76549320047d76549320055f7354932005ce7390932004ec76509320078c4350932005e671cc9320059e748c9320047e75d85320047d75d85320047e75185320047d75185320047e75d81320047d75d81320047e75181320047d7518132004be7418132004bd7418132004f67118132004f571181320047d76994320047d74994320047d71994320047e70994320047f74594320047f71594320047c70594320047e75194320047e75d90320047d75d9032004de73d90320047e75990320047d75990320047e75190320047d7519032004ee7219032004f67119032004f57119032004fa7019032004f970190320047f76d50320047d76d50320055d73d50320047f76550320047d76550320047e7598c320047d7598c320047d76d4c320053d74d4c320047f7654c320047e75988320047d7598832004be7498832004bd74988320047d76d48320057571d48320047f7654832004df764c832004ef764c8320047e75984320047d75984320047f75580320047c75580320063e64d53510063d64d53510055e73d53510055d73d53510057671153510053e74d4f510053d74d4f510065e63d4f510065d63d4f51005767114f510066f5498b510066d5498b510066f5398b510066d5398b510066e7558b510066f5458b510066e5458b510066d5458b510066c5458b510066f5358b510066e5358b510066d5358b510066c5358b510066d62d4b510066d6294b510066e6254b510066d6214b510055e73d93510055d73d93510056e72d93510056d72d93510057571d93510063f64993510047f73593510047f72593510047c70593510056e72193510056d72193510057571193510053e74d8f510053d74d8f510056e72d8f510056d72d8f510057571d8f510065f6398f510047f7458f51
  | 25 => 0xd420053d74d49420057571d49420047f76549420047d76549420053f7454942005e671d09420059e73909420047e75d85420047d75d85420047e75185420047d75185420047e75d81420047d75d81420047e75181420047d7518142004de7318142004dd7318142004f67118142004f571181420047d76994420047d73994420047d71994420047e70994420047f73594420047f71594420047c70594420047e75194420047e75990420047d75990420047d76d50420055d73d50420047f76550420047e7598c420047d7598c420047f76d4c420047d76d4c420053d74d4c420047f7654c420047d7654c420047e75988420047d75988420047d76d48420057571d48420047f7654842004bf7650842004ef76508420047e75984420047d75984420047f75580420047c7558042004f671d9732004f571d97320047d74997320047d71997320047e70997320047f74597320047f71597320047c7059732004f67119732004f571197320047e75d93320047d75d9332004f671d9332004f571d93320047e75993320047d75993320047e75193320047d7519332004f67119332004f57119332004fa7019332004f970193320047f76d53320047d76d53320055d73d53320047f76553320047d76553320055f73553320053d74d4f320065d65d0f320065d6510f320069d6410f320071d5410f32005d57110f32005d97010f320055d73d4b320057571d4b320055f7354b320047e75987320047d7598732004be7498732004bd7498732006766598732006756598732006767598732006757598732006b67498732006b57498732006775498732006755498732006775398732006755398732006775298732006755298732006766558732006756558732006767558732006757558732006775458732006755458732006775358732006755358732006d74358732006d443587320067752587320067552587320047f75583320047c7558332004be74d9632004bd74d96320047d74996320047d71996320047e70996320047f74596320047f71596320047c7059632004be7419632004bd74196320047e75d92320047d75d92320047e75992320047d7599232004f67199232004f571992320063e65992320063d65992320063e75992320063d7599232006ae7299232006b67199232006b571992320063e65592320063d65592320063e75592320063d75592320047e75192320047d75192320047f76d52320047d76d52320063e64d52320063d64d52320055d73d52320047f76552320047d76552320063e64552320063d64552320053d74d4e320063e64d4e320063d64d4e320056d72d4e320063e6454e320063d6454e320056f7254e320063e64d4a320063d64d4a320057571d4a320063e6454a320063d6454a32006ae6450a320069e64cca320074
  | 26 => 0x67671994520067571994520063e64d50520063d64d50520055d73d50520047f76550520053d74d4c520065e63d4c520065d63d4c520047f7654c520057571d48520047f7654852004ef76548520066e6554852004f671d9742004f571d97420047d73997420047d71997420047e70997420047f73597420047f71597420047c7059742004f67119742004f571197420055d73d53420047e7598f420047d7598f420047f76d4f420047d76d4f420053d74d4f420047f7654f420047d7654f420053f7454f420063d6590f420063d6510f420069d6310f420071d5310f42005b57110f42005b97010f420053d74d4b420057571d4b420053f7454b420047e75987420047d7598742004de7398742004dd7398742006766598742006756598742006767598742006757598742006775498742006755498742006d67398742006d57398742006775398742006755398742006775298742006755298742006766558742006756558742006767558742006757558742006775458742006755458742006775358742006755358742006b64358742006b443587420067752587420067552587420047f75583420047c7558342004de73d9642004dd73d96420047d73996420047d71996420047e70996420047f73596420047f71596420047c7059642004de7319642004dd73196420055d73d52420056d72d52420056f72552420047e7598e420047d7598e42004f67198e42004f57198e420065e6598e420065d6598e420065e7598e420065d7598e420065f5498e420065d5498e42006ce7298e42006d67198e42006d57198e420065e6558e420065d6558e420065e7558e420065d7558e420065f5458e420065d5458e420047f76d4e420047d76d4e420053d74d4e420065e63d4e420065d63d4e420047f7654e420047d7654e420065e6354e420065d6354e420065e63d4a420065d63d4a420057571d4a420065e6354a420065d6354a420069e63d0a420072d52d0a420072d54d0a42005e671d0a420047e75986420047d75986420047f75582420047c7558242004de7399542004dd7399542004f67199542004f571995420055d73995420057571995420047d74995420063d74995420065e73995420047d73995420065d73995420045d73995420047d72995420066d72995420067671995420047d71995420067571995420047571995420047e70995420047f74595420063f74595420047f73595420047f72595420066f72595420047f71595420047c70595420055d73d51420056d72d51420056f72551420047e75d8d420047d75d8d420047e7518d420047d7518d420047d76d4d420053d74d4d420047f7654d420053f7454d420065f6354d420065c6354d420063d6590d420063d6510d420071d5310d42005ae7210d42005b57110d42005b9701
  | 27 => 0xc7058f520056d7218f52005767118f52005757118f520047e76d0f520047d76d0f520065d63d0f520047e7690f520047d7690f520063d6490f520047d7650f520047e7610f520047d7610f520063d6410f520065d6310f520071d4310f520056e7210f520056d7210f52005767110f52005757110f520057a7010f52005797010f520067764987520067564987520067763987520067563987520047f74587520047f73587520047c70587520067776587520067764587520067664587520067564587520067464587520067763587520067663587520067563587520067463587520067774587520067674587520067574587520067474587520067773587520067673587520067573587520067473587520067743587520067643587520067543587520067443587520067572587520067770587520067670587520067570587520067470587520067561187520057671d83520057571d83520067561d83520067661983520067561983520047d74983520047d73983520047d71983520067561583520053e74183520053d74183520055e73183520055d73183520057671183520057571183520067661183520067561183520055d73d52520063d64552520053d74d4e520065d6354e520057571d4a52005e671d4a52004de73d9152004dd73d91520055e73d51520055d73d51520063f64951520063f64551520047e7615152004be74d8d52004bd74d8d520053e74d4d520053d74d4d520065f6394d520065f6354d520047e7614d52005e671d4952004be7418152004bd7418152004de7318152004dd7318152004f67118152004f571181520055e73d91520055d73d91520065e73d91520047d73d91520065d73d91520045d73d91520047d71d91520047e70d91520063f64991520056d72991520057671991520057571991520056f72591520053e74d8d520053d74d8d520063e74d8d520047d74d8d520063d74d8d520043d74d8d520047d71d8d520047e70d8d520065f6398d520056d7298d52005767198d52005757198d520056f7258d520047e76d0d520047d76d0d520047e7690d520047d7690d520047e7650d520047e7610d520047d7610d520071d4310d520056e7210d520056d7210d52005767110d52005757110d520057a7010d52005797010d520057671d89520057571d89520056e71d89520076671d89520056671d89520076571d89520056d70d89520047d74d85520047d73d85520047e70d85520067561185520057771581520057471581520053e74181520053d74181520055e73181520055d73181520057671181520057571181520063e74181520047d74181520063d74181520043d74181520065e73181520047d73181520065d73181520045d73181520067671181520047d7118152006757118152004757118152
  | 28 => 0x4c430065e6454c430055f7254c430055f7154c430055c7054c430053d75d0c430071d53d0c430055d7590c430059d7490c430071d5490c43004bf7650c430053d7550c430071f5350c430071d5350c43004df7650c430055d7550c430071f5450c430071d5450c430059f7650c430069f7650c430059f7550c430071e7550c430059d7550c430071d7550c430051d7550c430071e6550c430071d6550c430059f7250c430059f7150c430059c7050c430047e75988430047d75988430066e65988430066d65988430072d54988430074d53988430078d43988430066e75988430066d75988430066f54988430066d54988430066f53988430066d53988430066e65588430066d65588430072d54588430074d53588430078d43588430066e75588430066d75588430066f54588430066d54588430066f53588430066d53588430047e75984430047d7598443006766598443006756598443007355498443007555398443007954398443006e66298443006e56298443006767598443006757598443006775498443006755498443006775398443006755398443006766558443006756558443007355458443007555358443007954358443006e66258443006e562584430067675584430067575584430067754584430067554584430067753584430067553584430067a6598043006796598043007395498043007595398043007994398043006ea6298043006e96298043006f26198043006f161980430067b75980430067875980430067b54980430067954980430067b53980430067953980430047f75580430047c75580430063d54580430065d53580430069d43580430067a6558043006796558043007395458043007595358043007994358043006ea6258043006e96258043006f26158043006f161580430067b75580430067875580430067b5458043006ba5458043006795458043006b954580430063954580430067b5358043006da5358043006795358043006d95358043006595358043006bb4358043006da4358043006b94358043006d943580430069943580430063e64d53520063d64d53520055e73d53520055d73d53520056e72153520053e74d4f520053d74d4f520065e63d4f520065d63d4f520056e7214f520067754987520067554987520067753987520067553987520067675587520067754587520067654587520067554587520067454587520067753587520067653587520067553587520067453587520055e73d93520055d73d93520056d72d93520057671d93520057571d93520063f64993520047f73593520047f71593520047c70593520056d72193520057671193520057571193520053e74d8f520053d74d8f520056d72d8f520057671d8f520057571d8f520065f6398f520047f7458f520047f7158f520047
  | 29 => 0x63d74994530063e64d50530063d64d50530055d73d50530047f76550530053d74d4c530065e6594c530047f7654c53004df7654c530065e6554c530065d73997430047d72997430047d71997430047e70997430047f72597430047f71597430047c70597430053d74d4f430065e6594f430053f7454f430055f7654f430065f7654f430065c7654f430055f7454f430071f7454f430071c7454f430055f7254f430055f7154f430055c7054f430047e7598b430047d7598b430047e75987430047d75987430047f75583430047c75583430065d53583430063d74996430047d72996430047d71996430047e70996430047f72596430047f71596430047c70596430055d73d52430063e65952430055f73552430063f76552430063c76552430053f73552430071f73552430071c73552430053f72552430053f71552430053c70552430053d74d4e430053d75d0e430071d53d0e430065d65d0e430071d54d0e430047e7598a430047d7598a430047e75986430047d75986430047f75582430047c75582430063d5458243004bd7499543004dd73995430047d74995430063d74995430043d74995430047d73995430065d73995430045d73995430047d72995430047d71995430047e70995430047f74595430063f74595430047f73595430065f73595430047f72595430047f71595430047c70595430055d73d51430055f73551430053d74d4d430047f7654d430047d7654d430053f7454d430065d65d0d430063d6590d430047e75d89430047d75d8943004f671d8943004f571d89430047e75189430047d75189430047e75d85430047d75d8543004ee72d8543004ed72d85430047e75185430047d75185430047e75d81430047d75d81430047e75181430047d7518143004ee7218143004ed7218143004f67118143004f57118143004ee72d9443004ed72d9443004f671d9443004f571d9443004fa70d9443004f970d94430047d76994430063e74994430065e73994430047d72994430047d71994430047e70994430047f72594430047f71594430047c70594430047e7519443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f970194430047e75990430047d75990430047d76d50430055d73d5043004bd76950430053d75950430063e65950430059d73950430047f76550430063e65550430053f76550430063f76550430053f73550430071e73550430071d73550430053f72550430053f71550430053c70550430047e7598c430047d7598c430063d5498c430047d76d4c430053d74d4c43004dd7694c430055d7594c430065e6594c430059d7494c430071d5494c430047f7654c430065e6554c430071e5454c430071d5454c430055f7654c430065f7654c430055f7454c430071e7454c430071d745
  | 30 => 0xd72181540067671181540047d71181540067571181540047571181540065e73994540065d73994540055d73d50540063e65950540047f7655054004bf76550540063e65550540063e75593530063e64d53530063d64d53530055e73d53530063d64953530063e64553530063d64153530055e73153530055d73d93530063f64993530047f72593530047f71593530047c70593530063f76593530063f73593530063d73593530063f72593530063e72593530063d72593530063c72593530063f71593530063e71593530063d71593530063c71593530063f70593530063e70593530063d70593530063c70593530063d64193530055d73193530053e74d8b530053d74d8b530063e64d8b530063d64d8b530057671d8b530057571d8b530063d6498b530063e6458b530063d6458b530047f7458b530047f7158b530047c7058b530053e7418b530053d7418b530063d6418b530053e74d87530053d74d87530063e64d87530063d64d87530056e72d87530056d72d87530063d64987530063e64587530063d64587530047f74587530047f72587530047c70587530053e74187530053d74187530063d64187530053e74d83530053d74d83530063d64d83530063e64983530063d64983530047d74983530047d72983530047d71983530063d64583530053e74183530053d74183530063e64183530063d64183530056e72183530056d72183530057671183530057571183530055d73d52530063d64552530055f73552530053d74d4e530059e74d4e530055d76d4e530065d76d4e530071e74d4e530071d74d4e530055e73d51530063f64951530063f64551530063c64551530055c73551530047e76151530059e74d4d53004f671d8953004f571d8953004ee72d8553004ed72d8553004be7418153004bd7418153004ee7218153004ed7218153004f67118153004f571181530065d73d91530047d72d91530047d71d91530047e70d91530063f64991530055d73991530055f73591530063d64191530053e74d8d530053d74d8d530055e74d8d530071e74d8d530051e74d8d530071d74d8d530055d70d8d530057671d89530057571d89530047d74d89530067671d89530047d71d89530067571d89530047571d89530047e70d89530053e74989530053d74989530056e72d85530056d72d85530047d74d85530066e72d85530047d72d85530066d72d85530046d72d85530047e70d85530053e74985530053d74985530053f74581530053c74581530053e74181530053d74181530056e72181530056d72181530057671181530057571181530063e74181530047d74181530063d74181530043d74181530066e72181530047d72181530066d72181530046d72181530067671181530047d71181530067571181530047571181530063e7499453
  | 31 => 0x100200010004000002800100080000000000000000000000000008000000000000000080000001000000000140010008000000c0020000000000000200000000004000000000000180060000006002400000000010004002000400000180000014001000c000000000000040000004000000c001000400000000000004000001800000340020000001000800200000010000000002c0020000001000000000000000000001000c0010008000000400000040020000005003400200000000004000000000000080020008004000000000180000000008001400000080030004007000c000000800100000000065e7558f540065f6398f540047f7258f540047f7158f540047c7058f540065f7658f540065d7458f540065f7258f540065e7258f540065d7258f540065c7258f540065f7158f540065e7158f540065d7158f540065c7158f540065f7058f540065e7058f540065d7058f540065c7058f540065d6318f540055e73d8b540055d73d8b540065e63d8b540065d63d8b540057671d8b540057571d8b540065d6398b540065e6358b540065d6358b540047f7358b540047f7158b540047c7058b540055e7318b540055d7318b540065d6318b540055e73d87540055d73d87540065e63d87540065d63d87540056e72d87540056d72d87540065d63987540065e63587540065d63587540047f73587540047f72587540047c70587540055e73187540055d73187540065d63187540055e73d83540055d73d83540065d63d83540065e63983540065d63983540047d73983540047d72983540047d71983540065d63583540055e73183540055d73183540065e63183540065d63183540056e72183540056d72183540057671183540057571183540055d73d52540059e73d52540053d76d52540063d76d52540071e73d52540071d73d52540059e73d5154004f671d8954004f571d8954004ee72d8554004ed72d8554004de7318154004dd7318154004ee7218154004ed7218154004f67118154004f571181540055e73d91540055d73d91540053e73d91540071e73d91540051e73d91540071d73d91540053d70d91540047d72d8d540047d71d8d540047e70d8d540065f6398d540065d6318d540057671d89540057571d89540047d73d89540067671d89540047d71d89540067571d89540047571d89540047e70d89540055e73989540055d73989540056e72d85540056d72d85540047d73d85540066e72d85540047d72d85540066d72d85540046d72d85540047e70d85540055e73985540055d73985540055f73581540055c73581540055e73181540055d73181540056e72181540056d72181540057671181540057571181540065e73181540047d73181540065d73181540045d73181540066e72181540047d72181540066d72181540046
  | 32 => 0x40000000000000000300180020000001000000000000020004005000000100000010000001000000100000000000002000000200080070000000000400100040000014001000400100000010000004000000000080030004000000400000000000004001000000100000000014001000400400000020004003001800200000070004002000c000000800100000000024002000000000000000004000000400200080010000000001800200000010008000000c004000000000000050004005000000b00040010040002000000c00000000008003000400300000000000000001c000000c002001000b001000000000020008000000000000000000018007000000000300020000003000400100000000018016000000000140000000000000000200000000000002000c000000400000000000004002000000400000000008003001c000000800200300040004002001800100000040008005000400000000010000000000800100000070008002000000100000020000002000400000040040000000000000000000000004000000c010002000000180000010000000c01800000010004005000800100080000014000000c0000004000002400e000000000000050004003000c002000000100000010004000000000800100060000000000400000140010008000002000800000000000004000c00200000070000000000800100340070020000000c001001c0010004000000000100000010000000000000000000030014002000c0020004000001c00100000030004004000000000000000000003000000000000000000000000000100100000000003000000200000040014000000400000040020004001001400200080010000000004000000040000000000000400a00000010000001000c00000140010004000000400000040020000000000000100000000000001000000200340000004000001c0000010009000c000000400200000000000000000400000080000008000000c00000000000004001000000100100030008001000000000000000000001000800800100000000001001400300040000000001000c0000004000000800200080020014001000800100000020000001000c000000000000100010004007000000c0010000000000200180030000000000000200140000000000000000400000000034002000000200080000000000000c0020030001000000000000000000001000c002000400000140000008000000c000001c0100008004000000200180030000002000400100000010000007000000200000000000002000000200000000000002000800200180090000002000000b0004000000000000000000000000000400300040050004000000c00000080000000000000000200100000004000001000100000030000
  | 33 => 0x1000b0000001000c002000000200140010028000000000100000030000001000400000000000010006003000300080000008001000400000000010000002000000000080000000000000800100140000000007000000100040000000001000000600140050008007001c0020000000005c00100000040000000000c00100040000004003000000600040070000000001400000000020004008002c0010000005000000100000040000004000c0000024002001000000000000020000000c000002c00700000020000000000c0020000000000000200140000004001000000300040000008000000800000000000000003000000000040000000000000400200000070000001000c001000c009000400500100000014001002000100040000004004000000100100000018000000400100040010014003000c0000014000000c00400000010028000000400200000060000000000c000000400200000020000002000400500000030000003000800000000080010000000400600000020000000000000000000000000002001000100000000004000000000100040030004000000000100080030008005000800100000000018001000c00400100000000000003c000000000000000000000002000c00400000000000000000c000002000500000000004000000400000100000000001000400000040020004000002c00100000000008009001c0010018001000000000180000004002000000200000000000001000400200000010008004000000000000030000002000400300000000000000000000500000000000000000800500000000004000000c000001c0020000000000000100000000000000000000000040010004003000c0020000000000000000080010000004000000200000010000005000000000200010000000000c0030000000000800e0000000000000000000020010000000c00500000040008003001c0000004006000c001001000000080050000000000000000040020000004000c00500000000008000000c0000000000000c0010000000000000000000000000000000400200000000008000000000200000040004005000400000040000004001000c00100000010014000000800100040020014000000800000000050000000000000000040010000001000000000080010004000000400a000000100040000014000000c00000080020004000000c00000040010000000000c0000004000000c01100000000020006000000300000030008000000800000000000000000001000100000000000005002c00600000050008000001c000000000100040010000000000c001001000200000000000001000c005000000000000000014004000000900000050010002000800100040000010001000000300000020000001
  | 34 => 0x6536280851d2488752000087d20a20000000000198a1458dba00006821e6977c33d800099ba1500e588a82ca870c5179b5c000196400000000000268000000000008c6000000000000000000000000000047b0000000074626323a000000000000000000020a0000000000000000000000001f7003f8e2c31f000087880002a989b46d1000059f80000000d0a00016480000005000000200000000000000000000200000000000000000c003001c00100080000008005000400000080010004000001c001000000100000000018000000c000000400600040010004002000000400000020000001000000000000050000003000000100080020000000000c000001c007001800100100000000000000000900080000000000000000c0000001000800000080010004000000c003000c0120014002000800000000000000004000800f00080000004000000000200000000000001000000000040000000000000000000000000000000000000100040010010000000800000080020004000000400000000000008000000000000000020000003002c0020004000000000000140000004000000000000000040008002001400000000000018000000000300000040008001001c0000008000000000100000030004001001000000000010000000000c001000c006000c0080004000000000000200060008000000000300040020030001003000000100030004000000400400000000004000000c001000c00100080000010004000400000100010000000001000000040040004000001400200140020044000000c000001800500040020010001002000200000030000000000000000000000004000001400000300000004001000c000000800200000000004005000000000040000000001000400000080020000000000000000040010000001000000300100030004000000c005000c008000800a001c0020004000000c00000080000008000000000000000010004000000400200000010004012000800000000000038000000400000040020008000000c000000800000000010000000000800100100010010000001400000040020004001000800200000030000000000000300000000004002000c004000000100000000008000001000400000050000000000c00100080000000000000400000040010010000000c0030000000000c00000080000004005000c0060004001000800000000000004002000000100000000004000001000100040000004001000000600040000000000002c003000000000040000028001000400000000000000001000000300000010000000000000200000000000006000000500500010004000000000100080000000004000000000080020004002000000000040010010008000000a000000200000000008000000
  | 35 => 0xb5a36180008b9833c0000000000000000000006830000000000034680000000000000000000025ea7f5800000013b600023ce00020c80000000000154c00022f2000247a50b23160000000034800027008c221422c65351b9e000254a08e896a0000000007800000000004ca00000002214000000008ca74c78d9d306fd000034d000000000000001e906c58cd00000000546812aa9280000000000424926e845880e9ec23405fb00020a8168e8e197066058000000000093694640000094853000087e97580001ce000000009a203dc0000000734924c000068c000000000002d8000250a20300000001d9c0000d3800000006c7000033003f80000000000000000023203b9988e8cb1dae000153a6c293f48b08000000047000000000000000000000000000003e0977e61c128c000000044d80009c3800042c8ed200001c68ee000024680000000000000000074901dca6ba9d6236000000000000a000004da8000000000000000007b528f43c9937e00023d4000000000023360000db4000000000000000000000873000000000000000000000000000016b200000000001be43f12376000000045f200600022444ae83260000e182a888347a8a03c133800099b0774a5090566410ec000020ba7e980000001bee00020fe9a900003ca9ef200012846c8a064046284c0000000000000000003e6000277e000000075c800000000008e49fa4000000000000000000000000000000025760000000000251c39f20a499f9a2a2e9226407480005ad0a9a835276c000238466310284b4800045b294c6eea65287524005732840757000044780003bb25c20000000012919695f00000000000445800043c8000000000069026d010b286c73c972c51315004e480000ae06ec0cb1dba6ad0e20722a49a123a26a5c1018a81b84067579caa42980000002024000247200000000000d361cc05da27c9c5e0000000000000000000000000000000223200005ec5e880005a40000000193e6b18398000273600000003da104a00000000000000061165a0001ec800005f2a78800000001b20001d0200000000000dbc00022bc00000000000b9057917820000000000179600019bc0000000304800032d80000000000000000000005bc84480000001dbc00000000000000a13a1c002e000007b06ee000076200005228cf921400018b80001e4e000000000000008a400004b0000000000000000000000000073d00002c10a8e15c000000000003c829821fa9eea00000003cc8000325825e2988dc80b09444022811a6f31e680000000a70a46845c000000012360001dd8000185892000007e49e0a945800042d29d2452051417587f20e29efa93e8000464005e20500009c100004b78cae00000000000000642844400017b601500001a70000000161c000185
  | 36 => 0xf400009e200002db000000000000001326000000000023f60000000000000000000003928000974000000023d82b50bc88b480000001ff600000008498ef80000000000000000014da50a800000000000000000000000000010e23411e18a389dce000000000000000000000247234c0001d3e0000000a2d00006c8000000019fa7bb0000000000000000007ba0fb000000000001df20001f5a000000000000000000000508046a0000000000000000005c687380000000000000000000000000000000000000000025400000000000047e000179a883a24a000000037e800086f24ac0000000000000000000000000000000000000000000001dc0343800084c0000000000000008bc876800000016764c8000000007da0c58000575221800000008e61c568e51c783080000a5480002c5162c0000e2a6568000000027276603da0000000000000000000000000000a8d0000000129270c023875380000000000235140a0000c740631cfa0000000a7a8bd6000213864ca3aa0d20000484000032893a0817000039d0000000000082b8000a07800038ba35800025ac00003b056014be0411e62000182042b80000000000000000000000000000c2800000000000000000000000001b44da0cce0378a527cc8c102b428800710f9c59e8756877800031f938218b8000812827ca23934e85600000000000527800000020046f7800000027a8000000093e127a000000080d24a800029927ff2a3e0001e8252e90c85d700002e000003e980009570000000000083d007c000000000019924168000000085e8a1a44400000005b1800000000000b32702000000000000002cd08e20002546000000000000000000000420000000000000000000000000067c18bc0bb80006af983000023dc94f10420000a20000000000026546eda8b65d5800000000000000c1800000000000000301000040b23e800000004848000000000098c0000000000000012d4000000000000000000c6c35e80000000aae2ee000000000000a3800018e89c40000000000000000000003101d7c436000000011e069b800000010fc000011c93b800024328980001ed605f19b60000000816a6229331a6c6aba1789098dda2f2800014c0000000000000006741d8000067a800040806da00000000000da063d800000000006668000000000000000000000000000244000000004f8826e00000008c1000000000006ac053202180008a5000007080005dc00008f480002db800000000000000b2868c1dc4679000086680000001b6093887ba4f58000000166870188ec4c097ac3749f18a09000000000008298000083910a000000000000000001ce8000000000025fc7e80000000131012c8000000081c8f6800047f27f40000d8c00016240000000146800022e000000
  | 37 => 0xa002740000000000000000000008b280005cb8000000000000011c663d0000249063600000000001e4200024b812a0bc600010229b90fc0610a87461100006d000007740000a93a2e400000004271fda64c246c0001d6c00000001a9000000000007f019f24371e885c99d9a358265c6800f9457294a299e96f212a800000000002d580a6000064c0000ee80000d1e8bc00001a622389eb000060b8000000000000000000001172a1915fe9700000000000000000000000d00000285000000000000e608be18d80000000000026600012880000000000000000000000000000a8e24340000b5816d0000000000040989365858d680000f30a4511660000c68a6b000049395580000000000000052384a66750748000000064380002a00000000000000000000001d12000000000000000001a227d420384e323bc5640ef40001afa000000048f80001de0000000000000000000000000912a5e00000c6068e1d7000000000000d7298500000000d089d2800000001409e695881b8000000001a27c4000091b8000000090e2bf000000000004c58000000000076080003220e160000a240000000000000000000000001bb81f50000000000000003de68a00000001d506c9896600011a800000160000000000000099880007e393ae0001e1e000000000000004ec80000000000000000000000004b1000000013f6257000066600009a717c48fe000011500000000000000000000000000000aea000000036a0000065939042e000073588ee18680000001e489a4000000000000000000000088200000000000000000287a00000004db05b000018e4000126c7d20a9089e946217ba6960000000000000037d9da69e918340000e98000000000000000000000000114200000000001c200e500003d00b42510873a01b8000192800000000000002758000117e00022cc000000000005e00000000000000000000006e000000001772000114000022f426da7d20000b6800018e673f800000000000b2025827d0000000000090a06e802a8000000000000020560000000000000000000000002356000000041000000001a3e00000000000000000271025614e2000000000000000000000000157835b13340c80e761829108000000000012a400028d000000000000000000000000000000001f4488d8ab453a07a60000000a4992a214d8eac0000000000000000009e200025f26ff05f652998061ae1702755800000022b8485800000000008820d221af80005fc880200000000000fb600029f400000000000000000000000020b09b62a1c323800000000000ada09c8050000000101e00000000001642000099c000000000000000000000427a4fc9bb21640000a6c577800065a00340000000000000080224ba1ef8000000000034926705c9226c1aa00
  | 38 => 0xa8a00003e22c6a03ea468000000297800024e40000000000088a0001f2c85880009d98000000000000028f80000000a1100000000e1a67b80000000000000000078500049030c4a14f00005770000000000000029e6000203212c2984000057a47ca5e400000005d100000001f3a0001b920f60652100800001200000000000085000000000000001de00000ae81e300000002054016063400000002dd28849c5000063203d22cc0cf09d7800025e0000000292290900000dd1d3400000004291ae699600000000000814000000000009a68000000175e0000cba6658000181945699980008ab0c0a55d93ee0000b66000000000000000000fc60001d06000091400000005dd00008440bd8a7c000009e000000000003f6000023e800000000000001c1c00000000000000604a1820000000a89000000000008999e5400001d010c21c20001662147800000000000390000000000034a8688a0d000000000000000000000000000000007798000000103c0000000a068000000296c000125000000001db93fe000000000004a4492a550000000000000000000000000000000000000ff00000000000000000000000007c30000000294639e00008b6a38c1e48ba200020ce67009b87fc82de000000000025c8246000000000007471c6000016b023d86f233218e000000005a217ee85e800000012b06c608f07c20000669000000000000000000000000000000000000000a8a043a8eba1ca000000077b9cd41dc1dc665b9bc65cda55a0000000000000042d800000012be0000000000000024f8bb600000000001fe6000000004a24165121e1000c067a87f00006ef00004f48000a268000000000081f866e2620000231086400027c40000000000110065d000039900000808000000000000023900001ec60002722000037a0000000000044c072188a00000008ca94c43a40000000000000009f60000000000000000005b200000000000000000000000000000000000000000000005cc0000000000000000006f84821b500000000775800052300000000000000000000018e20000e280000000000000000023ba0000c5800006f69f0932e53780002160dc00000000000000000000000000f741d500000000000000000025180000000000000000000025d6366800000000003f795b2000168200000009f8a04c0001e6600005d06b51318190141610d23ca00001f425507aa000044800000000000000000000041100005b6131e00000005521b96000190800000000000000000000000000000af157a0000000000000057b252e4aa00009ad8ca80000000000000039ea40600000000000000836800000016fa000000000000003be8000060800063380005f09b0822780000001a6600027ee000000033a910c0941d7400024c400000000000c849
  | 39 => 0x54d00000000f60000000000000000000000a1c1976000000046e0256a9501aa00000002a08738000083a3e28132000211a1268b3c0002a3002421a06541450000000078099ce4fc0ac400000000000c1c0002a2e00006266cd80000000000000000000000002a180008d49dd23460116848029e7da000068d800021daa5a78f0000000000000000003a58000000000000021086ada0e0000000000000002e78000000210c00000000000000000053a8301a8000018b6000000084d800024b8000a900000a328000656000000012c2000000000000000000ed0000000073908ea7a81b48965a8b20000000000000000015ae000000000000000001d80000000000029380000000000063823c926400000001c81194029002a0000000000000000000009e5800000028ae00000005c2000035e12a6559000026800000000000570000000000000000000000000055d19a80000000384a7a000000005fe1d0c76496462b6000000000000002226000000000023d016d800000000000000000000000027a000000000000000c0e0000000000000000024220000000000000000000000000b963d88000000000081a209800e894800000002c392023659be893c992e000163400000006290e5a9f79d96000000018a8000000106a00025cc0000000000088600000008951e2e000000000000001ea00009b2a2704e88e7040c1e6a6f5a3ea49a04ac1f988d053e94a418100000000a760001640322809658a107200000000000000000000096f800000000009d00f980000000000000000000000000000000000025300009aca5da96b95506e41b54743800093408120000000000000013e0de03c60eee00000003f425a600000003ba80000001c2635200000000000000297000000000000ba8000000058889560858000000000000025b457680000ed2030a6a01084c700000000000000256213e80000000000000000051c80006e5000091300000001bbe00000000000000a560000000000041880000001f3400005c20000000000000000022fa86580009f68000906800049081b60c118280000000000086804d000000011c401397f00000000a0880007800000098000000014d600000000001c3c0001bb400000000000000000000000021ee9da800000000000002a08643000000000005c8000000000000000000a208000a74083800000000a482aa3719762a660000a5f0000000000000018887f10000317000000000005f980001a99eee6a4a72a81d88d621c8000765000000006c400000001f7821800007e4000000000000000000ecc00028e00000ad200000008af80000000b3e83e032400000000002306a2a000055b8000000000000000004ef800000000000000000000170c34080002b70ad693d8000000000036b8000000000072300005cd0
  | 40 => 0x19ca14800000006e1069e587800000025a434c00003e3000000005fa00000006ac800047d00000000000000000001c91bc15e0780090800015d800057880007ae19e69680ca07b011b07d726380000e5c3c1800000000000000f0a27715f02931e0c30698d64cc8cfa00017b26d31ca60001c840000000000000031c94d00000000000000054d88000000000000075800004240000000000000000011760830b3a64e02c40001494000000063b8a3e2d000009d120840001ca019b00000000000000029a000000000000000000000398a13200025443d380004e6000000000001a880000000ece054800036c800000000005bb988400000000001fcc0002498a7f1a78832800026a10180000000000283c00007d2000000062409109a31f0200002a20000564000163800026ce1d919b26d780000002592641a8c60001de20000cfe06f08a44b2000073b0000000000000025c49ff9466000000000000003370000841000000000000000000000168c2a20a500ae850e099260400017d000017cc0000026000050269c000000016ca00016c0000000061d80003f49936000000000000004bf884e4b2a95aa1e122a0fe96a450387902b1976427817946402500049966c05918de000000000000000000000000000000009cc2d1a08a4cf8000312000031400002da82e6000267400000000000000000000000000000000000000000000000000000000a439c5468e9412a9080000000000000084a563a720000000000011562dc1ffa000000082400000000000000000013080009c99c7081d057400000000001e960000000000218c0000e5e0000000000281000000006a6a49000000000000000000000027394283d589bc00000000000000a029ed00660000661019400000000001a46a5884f013f97b4000030e080000000000006b2000000000004409cca00000006f680000000000a7b80006480000019000000000000bc88300001a880000000327234a00004685832a220000000000000000026e04f280000000000167000043f800000026d2000000000000008cf000000000005ab0000000000000000005b423fa00000000000000000000000020200f5800000000000002202000000000000001fe0000301800066b856c0001aac00000000000000000000000000000000a3c000000000000000000000000000000025e8000000000000000000000000000000000000000e820001fb00001efe51b8000000000065f0000000000000000000ba0000000000046e81a80000bec000000000024fe0d2800000000000000000000000061d075200000000000a020000000000000000000000000000000000094c80009ba179800000000000000000000058680000001cc61e80d80000265a00000009868000a76800000000004c51f28
  | 41 => 0x7ee8429c6c000000000027fa0000f8e3ee00000000000993976c000000000020c68882460000000000000000000000000000071484b449e000000007ca000000000000009d7000000000000000000663a9a65f7a9c093705f80000000000000053900009650000000013ca750000912000000021a800000009e880000f303146f4a0220000000581800000019e000000000ac90da00025045da1edc0000000000000000000008da0000382000056922b2000000001f8fcc435028498e87142d100000001000000000023e10880000000000000079f04b814a80000df066000009d62b3823c496a8363ec800000014f40000842368968669780006fa80000000cd40000000000000000000000000000000081a000000082d000082e178e8978920551933a2248000000004000012b2612a4f0000000000000008901306000213a0ac00000000a1427f1e5899591b449d000000000004aa9ff07bf000000000000000000000002000001fc0bf00008b4000000029bc0001f0400000000001f9e00000000000364000000000000000001a1e0000000000000000000004cb0000000023400000000000000654800000000000001f96000072800029f850f0000000205814b00008f01e2670e8bee530850a1f1a2ba9818a4e15386aa5ee00000000000000000000021b000000009ec86841f115865d40e6a000000072f00000000000a8b000032515fa2c28ee2260800000021766fb1e5600016501bf0262043800000018ca000112000020aa2cb91d815411c2000000000023480000f1464680003fd80000000000000000000000000000000948822ca3f0000817800000002ce16e00000000000000087a2f9800000000004150c3e000089667104427f40d5e3dba0c4062000000000004ee80000000000a5980000000000791181c0001bf6000286e8ec8000a228000000000000000000000c544bf0000a91991463f000052a800000000000000d8ea8990521ed8d849ed800000023a4a930f90137278437100008ad1e9200027560000000a1581a600000006de8000000000036a9c9e329105e0000000672800000000000000000000000045817d83a300000000000000124424d1b7210808e000000004ba99de3e79a9ea0725643fc83ee4f1a08253fa33200000006d61cce01e28f27d600000000000000000013a846c000000000000007c00000000000044a923a00001c00000acca760000875aa480cc0e04000000000000000000000000000000017926bb800029800000000000855a58600000000001a648d9a6f670d9f6e0000000000000000028880000000000298a000194c000000000000000000000549000000001ee9f40000114a15e00001ac00024ea00000000000000000082e00000005558000000000000008a000009520000000000
  | 42 => 0xea81241380004be80000000000000000000000000000000087000000005c0000000000019d672427be03d800000026dc280292800000000000ccc921a0d628684ba61900000000000457295630b8bae18700000000000000000000000006c393fc00000005b900004869f780000000000000087b0000000171e3d3098aa7200000000000000000000002e20000000000000054a827a2e80000000000097d800000000000000000195000000017c0000198000000000000000000200000000000000f3e1a0000000017f4000049400000002ad80000000000000000072b114c13680000be0ea00001a8ca5128267b986ae806800a143000000013868601bb03d1800000009aa000000069480008aa00000000000000000055796fe000272e00000000000000000000000011be149a3ac6c11c7aa2f022a4ab8fee000000000023e466b23c608f9962000015a000000000000005c58000000000000000000000df000000000000000000247400000000000000000196c5211abc43d01b80d6a4643260000000000000000000000bea66880000000000000071a00000000001c2e00000006b880000000000000000000022d45428b4e0000b649550000000000043487fc00000000001c96745a73000000007c800008e228662b0937a650287248b09fe05ea43e24884e0000154e65e0df484a120e431000000026fc3ad8000000000000017f629c8000000000035d800000005540001b3a39ba4562dc8000a8d80000df8b2c00000000000000000000041f00002018000000000000000006c49d60156006a00000000000c806250000393824c000000000025d4000000002228020001db86a893c800000000002828000000059300000001cb80a980004560ebe0002350000000056a0000000000030e800000006b69fd940c5c88fda0fc153063a92d63e100000000c7064d0e4c2020000000000000008363f925ba62a262c0f09d64390170a0000000000000000000009361a20777912c00000ca3a700005efa7ea25900006cc8496000000000000000000000000000000000004678000509847a4018000000000000000005f48000000000000008160000ec21e7000000000000000000000238273300006b6000088780fc71a8000000030aa6500005d31a900e215fc68600000000000000000000000007ed80009d51370390a8b00000000000285270c8000a710dd480a86026fe17ca2e50c38696000074f000099d9bc80a309e63841a2c000000056b23703ce000000008ce8c98000000000029100008870cd8a8a86220001fbe000000014481860000000000000000000000000000000000001d800000002ca0000000356a87e7ee066400000000000000000016a0001cb42ae933000015160002a3200000000a71fc85c380000000000658000042e800
  | 43 => 0x251050d1014a3d800084526120000bd200000004a6863e000000000000000000000000099a000169c62980002fc800000000000001ecc00000000000000a8780000001e4600000000da800042b00000000fdc2fc0000000052800000000000000000000073d800000000000000000000104c00002520000ddc49827f82fe8d2e0a28a4055017ba80083ce00011e60000000000000038e0000520800000000000000000000000000019c6000240a000000000017d60000000904912832c82545cc8000000000064a24f40000000966800000000004440000000000000000000000000000000090f00007b1000000000000000f5a0000b2093b0000000000000000008c29e8c9288fca1b18dd0000067800000000001b7400000000000000000000099f000000000007d8a30e67e16747eb0000197963a00022126be000000000000000baa0a60a26a8e9ea42be84e210f000000000004cd94b2000000000000000001d2a00000002230a702e1800052d80000000e66000000000000000001f8277c000000022fc000000000000000000eb459389943d7903a000000000000000000000089000022700000000000000175410480000000f8610d8000000014696400007d90000a470000000149c000072a649a62a2b792e62b981e0000285c000000016403080000000324800055ca3fc62b8ff8000000027b108400000004828000611800000000009d400000000000000040a00012324978000000000000000000000dc20f5299e0001d145b887fa16811b651b0702000000000000002ae00000001dfe00000003f0800096a11229cc80004c39bd8000122e000192a00000000001fd800000006ca8000380000094f97e2326800000000007ab80000001538000000058c800033e0000000000072880000000000000184881a8000000000000000000000c2c0000000000000000000008cc02206e88a4a297243600028c20000000027a160000120c09da8386bb00006e2a50822c01500000f4837b80000000788825800017f0bcc1519404953800050d98660001b88000000000001b00000000000000000013b00000f348fb000000000000000e868a116a21c40e1c3cb80000000000000000000000000001cb27d48bfe07c000000000000000ee40ec8000000000049f80c800021420751c664bb05d245b91ea0000000452800000000000000a2c00000000000000183800000000003b822520a180007f503008df90a200024580001b9863e93948ac00000000000000000001c00002d480000000000a2715225f2097000024ce79e04d052280008a8800000000000000560000000061b000000000000000000824a67800005de0000a945aa00000000000000000078b188600018180001bca2b280007ef00000000a6e00001201b
  | 44 => 0x16940000000000000087980000001a249080000000231e000000009200003c89ae40000000076800000000007b380003c0000004c0b38000156000000005b3000041b067e56600000001c9800017401b78000000000078f97429f1826c00000007b7872462800002428000000000000000000c4800000006dc000077ea6300009de80000000000a73800000008ba0001696487000000017601af0b9a38998028fb8000000000033480000000000000000000000007621b14000083ca2e89ae00025fa00000000000000000071800000000001cfc000082c00002e02bc80008e8a9ec00000007d080006b7977800000004d41050319800035b800000006fe00000000000000000000000000007f82a3c00008e80001c8000000001ad17860000000000000000006f00ef80007009f98983a58e80406501248000000115e0001ace000191c00020e600000000000000533000000000000001f6a7028000000000000003ea0000a5600000000000000000000000013e40e0a026000000000000009bea79e7f780001410000295000087a80000dc28ce00000000001b3082c8000000000000018ec6271e866d68000000101c00009726f0a98e5089d780140000000165e2bf9da435080000000000000000000029e421f008e60100005671b7c61880005c500000000b7c7aa22480000000000000000000002c580007208000843800000000009e411d600000000000000000000000010c262f8000000140856997e411f1aca8c31c721e380004ad000000007dc000000048c15940000000284800000003e40000a0a50b8aec9c31810000208896280005bd00000000000142000017a80000000000000000032780003f98ff41471b0000000003108000a6d9e2a4208df225ba0fc1c700000000000441101a703205200000000000000000076c9860000a231e3a0000aa41ffa97a040a3802e30000000000000000009cd27a691717a851e80000000e1e00003b65f812d80000d12449000000000006598000000020800495c200000000f11a7622a845a00010944f0000062e97d4000146a000185c0000000000000000000004dca09a0000dbe000000000000003b2800037e181a000000000000000000000000119c00009fa0001488027221a00000000001d3a000000044e1c14000005a000000000000000000c4617f80000001d0800008de0001f9c00010784ea000071400002c18000000000068180001358e504a19fa89b226ae0000000000144a0000b1e00000000001eca742a6ac000285a000000089680000001e8000000009d091cca8525689dd0000000236e6d88000000000000027e6a57000063c93c4359800000000004bb800000016ae5f718aa33d0aa800027c0355000059812f616a000094600006da1a5600018826d480000879ac000000
  | 45 => 0xb1000000000000000000209e000237c9560ef24c8800000000000ce9ddc000072600008ca9b3000000000002611dfc000000000009740000000000000000000006aa80009fb0000000000000000007fa0000000107a00016ba0000000000000000000005e426b40002288000000000000000001a980001130146000064780000000000756a90c000089a613984c00000000001568000000000014f67ab000000000000002276000000000028160000000086a1dc59e0000a8680000000e36000000000027dc57a800057d00000000000a0a80000001e0600000003a90750000084600015c8000000000005200001a6a69f15060000000000000007d800000014ae000000000000004449f1a00006e2000000000007c00000906265800074000008a708e400018cc6b70000000000025686203a48bb069697b05cea51256d1402a41900c3950000889000005d000071d8000000000000000000000000000000057e00000d600000da1f6000010c08fc1e380000000000000000003f4000000000000000000000000201e982800053816aa8f7a14a531884820fa61c5de8be85cf000081f1e5e85fa296000075c6259af60001b105b709e4000035030ca3100001db63f505245440c6e00002c624a000000000008de800014e0fb400014e60001f8000019b0000000000000000001ee094c037200016e800000009dc00009670b261530d0600021069fc80000000e220001f26563000000000000000000591000043a800002c95d200026bc000000000000002f6800000000007c3986e0001a4489080000000000000000058280003f3a11e43b00000000000000000000020a00000000067000000000005b50af60000aee000000000000000000000000000000000006bc800056f0000000000000013ac6db80002e9800000000003a10000000000000000000000000449994a0000000a6a8000000000000000000000000000032e0d7800035a8000000000000003760000000867800040da8d23f880003548334391800000010a000000003ff000000001ca000164a7088ae242193f80000000037076a178800094b0cee496135ca36296a437848282f87f04860000026000079b01720050c4e000000078580007c79a962e08000000229e000000067418e8a8580000000000000041a52585be4d212da8c51df86d195d89b688a65a983f2000000005a11ee2a6000000005804c489023d498d20000110000000035610a800000000000c3408c000000000008a3800000000000000006000039c38080003dca92404ea24c9ca262e000070a8c0222e7d28000000138e69500006e08d2838f086600027868038f2c584a51418580009a8000000029f6a538000000107690722dc50e00000000000199a31c000027e88f8000000296e000000000396de00000000
  | 46 => 0x4f80000000000392000095c8000000000037f800000000007aa8000000000000004660000e322e70e3e0000000000000079b8d2c0001d221b280007ac200c269000024a8708000000000000000000092a4d80008b3935837b093200000a8034000000013d4000000030580000001892000000000000f23ef00c2000000029080000000000000219c0001c7e00007aca3f89440000000a2e14ce0000000000019200018b27e507f42d88000000000011000009afa60c99212e45a683521b3800000026729f8000000022c80000000000000019c000040c80000000000000000000021ae00000000000000000000000000000000fa40000000000000000000007190000000253654500002fd800000004b600008ae0000000000000075d8000000000090b1298000000000029102e4800000029dc579800023683a6763000000000000000000000000000028da00000000312646000000000000000000000000000096c053e51f000000000000000000000000000000000000f4400009860000000000000049480000001012000000092a82460ab8000a0801d6000162000000007ca800074a06763671e9a00000004e9a0f00760000000100a8d89a0a60e12407cf000000008b200000000001c9c000075e373a16e000180e0001d4c9ee16106a3a8545f6985e4791f40000000070a8000784a4bc1098000a682012793031018c80001a500008a000000e4862889b9bae00019bea5d0000000000000004cc0000000a8800000000c5e6c3000000000002dd941e7a98cac00027160001eb22779bf2000180800024e800000000001c188a28f76000292e0001a86a6589ca9d80c906ae80007bd000095f80003a29ba000000000001b8600010ee000195c86492702f4000000000000000000000000069ca668000000000028dc4ae00000110000a03800000000001b4898092f800000019da0d9800000001ba000000083b00000000648000264c230000000017ce29180007838000000107e00000000001e709bc1b240002570320800000000000001d3600000000001b423d40d627ff917800000000000000000000080d9446000000011800005a28000000000063696d20c792dc869000000000006da800000000003538490000000000009b01b205948dd000056580000001f5601b235a40d0000000000000000000000f020001cee3fa80002be0000000000092480000000000000000000000000000000139233a925940000000005a800001691de80000000000110e000093072a000065100000002378152a1be03000007e3289200000004058000000086e000187c000000000000000000000888800023f8000000277c00000000000000000000079f802e0001d2e00000008b8103e000000000027fc2b90e5894080000690000a528e5200000004dd8
  | 47 => 0x129c391188052a0000000000000000000c180007eb8000a8621c80180000000000000000009a8884471306440002876000065a1f8000000007e80492694014800000009d273e0d9e00903e80000a0400000006a8000000025de0c69b4e00000003358000000228267600002ab26ba0001f14000000005d8000369800000000002a592a000000ae0000000000000002d91448e580000000cca0000000000064e00009160001d1095a80009f900009d180000000e0e000197255b000000000001cf00003e212b621680008f11584589800000013564b180009bf80007169f3e00000000000000352a1c400000000000000000000000000001cb83b80000000000000000014f834582d00000000000220c00880000000000000000000000006460000768a1740000488000000000004003c108563111f3671a0000000171c00028c40f1800000015b6000000000000009139dc2000000081194587c700fa00000008e38000650847444d0b7a8a6930065191da3b1a78a00000000000f4a24f00000000000000000000000ce9c48000000157e8f993549599e2267f1e8a955a94831a8ffa00000000000000a5a02fe99080000001b027bd80000000122000000000000000000f3600000009940000000048aa4e81540000000000000000000005d2800000000001b527bc0000f080000b2207a00000000000366000000027aa89623b400022ec00000000000c30000000000000001d3000000006d676780007970000698011e0369912000234e00026347111432403a01822b18322bd24ca000000001300006f70000000000000000000000000000000000000000000d50732274800007342132682000127c9ce0000000000000000000001d7e00009be83ca9fe5c609ea1ee00000000f1a00000001c5800000024c6233141a17900000001f0a00000000000000000000063500000000000a670c08000000000000000ce000000000000000000000000000000002b8011200000009dc8000000071e000000000025c6000154aa6222301378ce80e6a66a240000068080003bc1a0889899e200000001eb965800d80004fb00000001d46000000000000004e7000000000008bf9c2846080000000000000000000006cc38900000001064a1a8000a819fa20000bf853499fe568000046ca8aa000000032f8c22980000000000000000000580800017a158a00000008c0aa006dd877200000000000000000077a0ad11e833ca2060eea6ee9c22322000000000000000000798266000000028e6726825a00023d6119000000000000000000000045c00000000000000000000000010e88b1000067300009cf0000000000040e0416600000018f005600024c80000000a48000014d015690100002348c8ca5416c44e9000000006b200000000000000000000002f25dc
  | 48 => 0x9140be400000007980b120ff8000000000015a80000001d26000141400015aa000000000014c89ee8000a830000790124858600000000000788000000000007e6a54800000004fa021200000e018508fc00001f80000000000000088b1c583ef80000000000000000057a00f46cf123c9b19ee20db05846b11ef089703a03eb0000000000000028ee0000000000000000024d47f715ce000279c8981d8aa7e8a92000000000000008fc91de713800060e8000000000000000000000f6c000000000015d60c6000000018983cf0ac824e24520000bba5af2644160800012b800000000000002a04000069a0000000000000000000000000000000000000000005800000000000000000000001cb67e116f886c8000a40225600011d40a9000091f80000000ede00023c200015f21022318474800000000000000000747a7e860f2442000000000000000000000000135a00000000000840000000000000000bc000000000008d5116800024ae00006d880b11a400003800000000000268600000000000b0c00700000000de400020a882d80000000000a0e80004f30000000000000000002640000000000075280001a2a04200017bc985941c902000077ea2920000000000000000000000001e9e00000009041ae010791dc00012548b600000001cf028d2700736000000012340000000a4b293c0001b9a000222800012e077a80000be800000000002c71b6400026080000fe87d30000000171a9bd00001b9000052600000000000a000000000000000015f60000d4609119a6000097c57b80000000000000000061e00000000ca600010982858288a911200000000000000005c0000000000000000000000000044b800086e00009be0000000000061f800000000001d2872c000000008d8000010930a0000af000000007ee800041c09089380b001ef1c749e4800000016b6000082422d00004dd000000009a600000000000000000000000000000000000000000058a800000000000000000000118a7aea1e831e00009f600000000eda000000000000000000e340001bce00000000001aa6000000000029ba0000000000000045e926a0000000000000000000002f0800000000be0000000000000091e00000000e9e8a31b7066aa1400001db27340eb868d0ce400000002399e0434300000000000000000000400005b580000001d2c2f5077c0001bc400004ca0000000162000000000000000000a6c80002b680000000000000000000006c03e0000065e93e000029e0000000c00027ca30d80002028000000172800019947370000a6888dc00019240000e9a00005989c61c085d2000000006180000000648800000012721e7800000014b890c00e231da04800000000000000000000072529be000095e0000000000000000000000000000000
  | 49 => 0xbb205b2940000000092c822239c800000008624618cfc264800025f91323b5a6de2960000a1f000000008740001d7a00004e893480000000000052800000009da0000fc800000001f300002cc800085f0c1e0000162000000065580000000000000000084600002df80001b4268ea35800000000000000da442580000000000463041c93580ba204000027400004ef1dca55118b0000055a000149a2d8000000000009a79f8a0ca80000000f1600000006988000000045813b939e00000006f51d1a000000000000000000000a1a02ea00000004a0800007a8000000289042c0000811291e000000000000002f70000637278000014a000020e411b8e886ae11ae5810000000097a00003bc0002216000000000000006ea80004f729b047d800000010f80000000000000000000000000a38a59058a0e31670a77800000000005e9831c4c68efe7ce1fc2a0ca4545c4a9321ac0f5836400003e80e307108dd600017ae35000005a49c1a00000000000b02000000069d00000001f7c000000089a0000a731fb200000000000e3a585210200000000000000000000000000001f095823310000000000000000000000abc000000063e215ca0601060000000000000085a800080e80000001e4a7d180008ce00008e7178c5ca817851da5b80001daa1729eb6000146800000004d300005668540000000000001be000000000a03863788b4883e8b887f4800000000000e41d68000048c7c48000000000052c218a686a19400000006eb08540001faa0000a1002c00006ba0f7e207a2a66cd00001b980000001f0600000f000000001d6835416301700d30000000000000000000000000000000071181e225828c83398000000000000000000001de401d2438763800000021680000c2a59717fc0000000000000089c8000000000076b000000020728f8800079da27482b00001c4840e4540c3c69080000001dcc206124668388c8947878a1b09d18000000087e10e612f9afc00000009e3849e000052e000282e4fc800000000000000d1ca7a000067d800000000000002462a1814401d3a08c4588ab271700004a41cae000000000000007b08b5e00000005ff84c000025ce9840eae0000000000000073a81e422000000000000000000088a8000000000000002269d380000000000000000000000001cd8f120000000000000028da3347300cb8000000000000000001a9c00000003ae800060980000000000000000023d00008028000000195e55480000000000000000063f80000000000000000017118a296f000000000000000000000000000000000000000000000000000000000d4c000240e703856860b000025d8000000212200600000001630000000000000000000000000078498fa48a0538e060000000000000000000000000000000000
  | 50 => 0xd823318000000019a97984ec00000004010000079a99a000253400000000000bac29a00089b50000000155c059a35e000000000011fe04b1fe400018226b4a8a2419981e5a78abe000000000000000000000000000072924842011db4000000000000000000000992829055500006baa0f652f1b1e000065c1ed0000670a0d200010ca87f966e567993a00000007610ed49280e7e85b000077d824a90b870400000000f0000004300000000000000000000000008938000441800004e000076180000000000426953e689822e000000021c00007d50dde093849c000000000000000001502000000069e80000000000000000000000004c203a20000000000000051e144e930018000000003e580000000b781cf932a0000000787000081c269800000002f0204ea301fe20de213c4fa80004700be0000000078900000001002000000000019860000000000000000000008b000000000000000150469a00009118fd600000000b59ba600000004d284f637f0a1c00004c62a3000000000005e00000a84a1243381cda296800086d99dc3ea8000a0b11e20000000000293ea6e000000000006b08f28722242a8250000000000000000000fb0000000000000022de00000000000000a1200000000000000000068419c80000000000000074c9aa4000000000000004d998407e409508371ff86d59bfa9fc1c1000028be00000004c3290800000c65958000365000000000000000000000000000000000000b18000000000000001760000000000000000000002640000089850f80006279d6263193de431a75a00000000000000a4c00000001710173800000019b442f00009e611ce0f207d034980000d3800091d9ebc309800000013d037a8000972888e900819e85c0f7c1f3885c0000000000223400015920001c6e17c000000000006972a584680832a3a000000000000000000000297e0000000000035c000000025080000002154000000000000000001ef8000000000020620002916000236c6e3000097e0204000000060905863bda3be00006623008000131227e000241e98f1470000000039a00001820328000000013f173e0000000315941809a80007720cec66e00000000000218000000000005e28000244997e165a51a92717a4000093a0001296000000092d1f881118ec40000000000134271f0a1800c867c7fa83a800000000001b4a241000000000001010456128000000000003e6a776963000000000000002204755000000000005b0800006b8336916a1527cb81de76800000000000297a372a0300f80001e7202106a00000000000000088f00005e12990000000000b00000000000000000000000000a08000000092c41a000000000000000000139800012f056e7410000000000000000002ac0000000000000
  | 51 => 0xa0f800000000009508000418000000014ac000150e0000000000270a385003c0000b4c0bb0000750800000025b68d900000001b787378000000147e0b68000653aa020001f6656e0a789db9c2c15715200000000000000000000000000b240001a3c0000592a11800000000000001872000000000000000000000a4a8e80634000068599886b40000000000097c1acc53a9f246ea12565f1a07a515055e861a01ca2780d8a408000168a3b64390f5400007400000000000000000000000000000796870026b106e01a024020a15b00000b505dba0d0000000000012cc00029860002632000186a0000000000000000000001051b2c000250c0001ce246200008e780000000000000000000000003b61be20000000a412190941904834c810a47e02062e38a2247280003a3800000000004988000000000082f000034f800000021f0000199000000008330114a298dac2ed0aaa00014f245d00008ab80000000dd880a193c517000000004d83958cb08d100000b5000070900000000bbe4d10144a2b252a00000006df9902000000084aa2e865a939607e80002a1005c0a5288654f1fee00004f26550bde92c108e7f18cb43fc0f70000000078c8600000257490613b43e880008f20000000000080ba2ea000082600000003daa782a3924a4351034400000001fda5fe000125c8f825a29c909c60000000026807a000000000011fa60f873257100000002976000000000000000000000000162e000000000000000000000000015c00023b05dd800000013d846a800005f800081000006ce271a000000000000000001ff4000101000000004df12244d002f653b882a61e8d7e2f39a4a3c30a3087c80000000000925000000000000001222000241400027d4000000000028cc000000058f80000001e8e00000000000000000038e36c00000000000000000000000005168000a1780002708000000000086a980c0000000000000000000000000efc549a11c56e8510a3b03029279d5212890d64669152578033200000007ed0cda674919261a12f87218624a4600003aaa4de72e8000000000000009d80000000000000000000002c201fe000254c43385ba9b88c0c00000ea91c0000a729ed80000000000000000000008638000a7c8000000000000026a600025d200000005568000000000000007ec78687e23b700006a500000000cde0000000776a6c400000007de800063c27cc1189dec8198a0e1e5042a1ae952c6c6a55e66ea0ea000000000000000578000020a57800005f4000135e712800000000002a7000072f80009aa0000000003e5bc151285100000001bc06aa00000000000000000013200008718ea8338800016a8000000000000025840001c009da0fe0267986016b913c000000042288be87d840c1a5a5980000de600000
  | 52 => 0xe000021f816000000000000a7e00000ac44f81ce518291267b121e000025c463800000000000000000000197078a000000000000000000851983689f0db60000000631059a04d98c0718800000013380000000000256c0001a2e0000000000000000026640000000000043274800000000000000000000000008ad85623218f421e8974674e00000b705e675127ae9a123fe0001af02d70000000000032aa71c000062c0000000891868e0000000967800000003ae000000000000005ce064200000009ed29a400000009231fec54c914653008a253f0000000179e000000097b11840001c120000000000143a1e580006ec9e0800000d470f93848a900000002602456a0e2000192c54304f429f28141e92778000000037a18540c880008360000000128e0000000268a9b49239a3231e960e4f39f5e0198820345066a0000000000000035703aa00026ea4170fba000076881e0000000000003a0000866000000000000000000000179c000000000000000000a2800000000000000000000000000cc000045e00000000000d920200b8a0000d3a00014b49d90000000000000000000001c34000000092080000001b3e705976a81b0000224000041d102e00000000002328402253a000000077d004600000003eb8000a959766868aa1059a9ee4000000061413240001cc24c109f09cfa12c2d280000000000258800000000000000000000000084b80000001f868f314ca43d89ee423057200003404d18be2000000000000000000e0a121800000000000001410879175a5a00bf48e9a8a41a18a9e3de16366a10000000000000000001a4000013500008e2821075b92e8000000026c8c64355833e000000097d208e8d1a1000000000000000043828303309a480001ad60001b28a9424a61548000000000000000001e18000000000000002e400010d0050800000000001ab139a4998000000000018c00003c90a0810422aa7c8a01600000000000000000041827228a070e1e7428b8000446800000000000000000a1880000001118000000000000ee00014ec1ec2588862000000012e29d8a9729cb00000000000000000018400005bf0000000094a000000000003564d8800019180000001d6600022d6000256e3a50000000000000000000000000000000000000009c1800000011d000000009f200003d7000052011549b580000001c48108a80400000009b980007dd914e1262628000000000005420001f160000000000218431483f600011a20001be000000000d802ac29e8000000163c000174e7a1000000014908b89b6c000000010f80000bd116a91980000000190000000000005440000000000015800021720001a4c0000000000000000012f0000000000000009581654000000094e00009480228667000000029800
  | 53 => 0xa01800097b800075616ce694265e000136443ea9c6000000051480003af0ea6035a25061480000001528000000000026c04bca3f400000000001a4e00000000000aa092d80005d4800000000002920dcc000189a00000003ac800013493aa856808c960000000000000000fec00000000002894208800000000000000000000000060a870600000b4299000000000002ff0eb04331bfe000036e00007444451f7400000005b80b8400010aa18780003c709f800000000000000000000000026aa0530d3c000000000000000000a1e0f8000000000000002060000000000022f600000009ac000000004288d0800019620c283b920606801cc22229347a507227a600008800566000000011ca20a4de13fa5991dbe0000000018aa5209c221091f15426e3800000005060001cc45cc0000040157c568a166668000042f80000000000000000000000000000000a5780008a800000000f0e000000021e00009f5a4324db8000a3a800000000000001f6c0001e5087623600000478028000000000004bd0000000085212107d80000000000000000000006d98000547000052180000001666000000000007d6253a13e00000004720cbc36211800eb20866cba2ee0000c1406384760000b5497624e60af800000000003ce800000026f200000003b200000001e7a0000000000000000000007cc13e66e9000091aa8960000296000000084d08947d380007238000000000000000009439d9025b09ba2750fa836e00004af02c0000000096097a07af800068480000001bd00002298000000019a0438652000000000006c180000000000000000064580005af8000000000000000000001e528748000000058e7ad16ea837a66000000006e700000000c0094a0000000098e039a68a8c213c234421e0459167c489800086e8000424000000000009490000000000000000000001afe4ee1e301c3859e140000055aa8fa78d0d701849db000014304e29ed2602a32e9ce800000000000000000000000061680000000000000000062b000000005a688e8d6443c000000000000001280000000000000002210000120000000000000000000000000000001f20000000574152e00011ac000227800000006b68f6600000000000000000000015f000000013da2e61652000000000000005248000869800029d000028c80004b4261e0e11f7e00000000f292ce000000000000006fc0000000000086d000000001480001a040001af400012388d700003c402a8000275200007c82ef136000000000000000000151e96a800000000000000548a350000000120428a800000028f00001424667a6240001a82000000044e800060515180001f7285397aa000030c000000000000003188000978a57a0001406559a6360000ffe62d284200029540000a060000
  | 54 => 0x86b000000000005b98dca7b68bc40000c4c5e21a8aa12800000000009e50000000157000000000000000000000000000003de8000954800000007b200000000001d6a000065635f05dc00023247079c400000d2000000ec24794dc000129e00013801e080000b49d40000069200000000000c24112a3120000a0ca429508000000000000000000b360000000000000000021d0000252600019e80e78742000271e9ae0000000096810b80000000000000000000000000068000000000000011984160000a828000172104600016b8250000096c8000571800018328581558a3a70116f61139e6459c969831696c804b88b600000004ab00000000000000000000000000001294000016e00000003c78000000000000026923e480008e696ec00003628c6877635d1a1c7f2a6261ba800000019f4000102a47c000044703a46231be64698000249800048a1da80d185d439b000029a85ac8da80000000000000122049d8000000000056f800000000001bd0ea238313885589a149309fce582102421b20e800017e80000000000000000000000d0a6c200028de000198221a800000027ce64400000000000775000091780000001c929e32a0e5a10000362a3a8a58000000000001d9a43a0000000000000069f9ce63d90000000133c63080000000000299a62000000000000ac0000000000014f0000000002880000000000000000015f8000000000000020804d4800000017ea0001cb05b6845000000007a7000000000004a297fa000000000000000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x87686dc951440010ed0f312a28800299a0a625451000633b90c4a8a2000c668718951440018cb0e312a28800389a10625451000712c20c4a8a2000c67741895144001c8d06312a2880039160c625451000633b98c4a8a2000e6180189514400126b08382a2880025560c7054510004b2c10e0a8a2000c64621c151440016c304382a288003195d4629051000662b98c520a2000874865d541440018caea3128288003195d4628c51000652ba0c518a2000874865d531440018caea3126288003195d4628851000532432a510a2000c667654a21440010e90cbaa4288003195d4624851000437c3ec42822000c2d74d88504400189ae7b10a0880021b61c621411000616ba0c42822000c4d7318850440018cec4b88a088003191897114110005b1c12a31022000e606254620440015c50d10c40880031a1d95248110006383b2a29022000ce07648520440016c30a90a408800319dd462841100042ec1ee8b28200083d84dcd65040010db05b8aca080021760e75990100050ec1ceb3202000a1d839d564040010bb07bb6a80800217e1973d50100060f322e7aa02000c1d645cf540400107b093acc608002876127598c100042ec3ea93182000a1d849d563040010bb0faa2c6080020f61376d4c100041fc32e9a98200083d87993530400107b0eb26a608003075d263d4c100060eba2c7a982000a4d83d52620400145b09a9cc4080029360f545881000516c26a6b102000c65751c562040010eb02bb6a4080030d99171d48100061ab22e3a902000c56635c752040018aac6b8ea4080031998971d481000632b12e3a90200087586dc5520400186ac9b8aa4080031558f715481000632b16e2a90200086d829d6610400185cc8b96a2080030b59172d44100062731ae5a882000c4d635cb51040010db0f316a2080021b61d62d441000532c32a41082000c65765482104001c4ac8a9042080039158d520841000638b2ae01082000cb1645c021040019a2c6b804208003385897008410006b0a92e01082000877865c6500400186ac8b8ca0080031558d719401000632b12e3280200083d84dd850040010bb07bb0a0080021b60b76140100043ac0aec280200083f865d0500400107b0f320a0080020f61d64140100042fc32e62802000c1e645cc500400183ac8b98a0080021761e63140100060eba4c6280200085d8758c500400183ae8b18a0080021be19721401000617322e42802000c2d645c8500400189cc6b90a0080031358d721401000436c3cc42802000c2d74988500400189ae7310a0080021b61d621401000616ba2c42802000c4d73588500400186cc8b88a0080030d59171140100062b31ae22802000c55635c450040018ccc4b88a00800319589711401000632b28e48802000ca5641c9100400198ac639220080023921d6244010
  | 1 => 0xac9b92a2100031358f725442000633b92c2a884000a65865442108001c4ac8a8842100039158d510842000634b2ae01084000ca9645c02108001992c6b80421000358545700842000437c32e52804000c2d645ca500800189ac6b94a010003195c961940200041ec26ec280400085d83dd8500800107f0cba0a0100020f61e64140200041ec3ac8280400085f865cc500800183cc8b98a0100030759173140200042ec3cc62804000c1d7498c50080010bb0eb18a010003075d1631402000617322e42804000c2d645c8500800189cc6b90a0100031358d72140200043bc32e22804000c36645c4500800186ac8b88a0100031598d71140200062ab1ae2280400087587984500800186ae9308a010003155ce611402000632b94c22804000c357458450080018aae6b08a010003195c9611402000632b28e29004000ca5641c5200800198ac638a4010003195ca71997100042ec1ee8b2e200083d84dcd65c40010bb07bb6a9880021b60b76d531000436c16ecaa6200083d84ddb53c40010db05bb6a7880021b60b7654f1000533414caa8e200096582dd951c40014cd05bb2a3880025560f74547100049ac26e6a8e20008768798951c400126b08382a3880025560c7054710004b2c10e0a8e2000c657518921c40010bf06ba6cb080020fe1173d961000532412e3b2c2000c1d749cc658400183ce8b98cb08003075d1731961000616ba4e432c2000c4d739c8658400185ce8b90cb080030b5d172196100062739ae432c2000c4d735c8658400186ce8b88cb080030d5d171196100062b39ae232c2000c55735c465840018cce4b88cb08003195c971196100042ec1ceb324200085d831db54840010db043b6a9080021760c765521000436c10ecaa42000a1c83591548400107b093acc7080020f61076d4e1000436c10eda9c200083d841d953840010db043b2a708002872116354e100041ec20eda94200085d831db528400107b083b2a5080021760c7654a10004b4c10e0a8c200087587d9421840014cd0ca9043080031cd95700861000671b12e010c2000d61525c021840016c702a924108003585487148210004f143e42904200085f835d3654400107f08b9eca880021de0572d95100041ec20e032a200085d831c065440010db04380ca880021760c76d51100043a432e3aa2200083d841db53440010e90cb8ea6880029960475d891000526c1ea9b122000a2d84d4f62440014cb033a8c4880029360f541891000532c0ea83122000c8d745cc624400145b09a98c48800299607531891000634baae03122000ca9745c06244001992e6b80c488003385c570189100043a432e3a922000c64625c752440010d90cb96a2880021be1f62d451000436c38c5a8a2000969821c151440014cd05bb2a2880025560f74545100049ac26e6a8a2000
  | 2 => 0x77654b20004a6c1ee8a96400092d84dcd52c800125b08382a5900025360c7054b20004b2c08e0a96400085f835d3658800107f08b9ecb100029920572d96200060eba4e632c4000c1e745cc658800183ae8b98cb100030b9d1721962000616ba2e432c4000c4e735c8658800189ae6b90cb100030d5d271196200062ab9ce232c4000c65729c4658800186ce8b88cb100030d5d171196200062b39ae232c4000c55735c465880018cae4b88cb100021760e75992200042ec18edaa44000875811db54880010bb063b2a9100021d60476552200050e41ac8aa4400083d849d6638800107b083b6a7100021d60476d4e200041ec20eca9c4000875811d9538800143908b1aa7100025c6047054a200041ec20eca8c400085d831d951880010db0fb2843100031ad957008620006b0a8ae010c400085f835d3654800107f08b9eca900021760c76d512000436432e5aa2400083d841db53480010d90cb96a6900021d21971d4920004b8c08e0a924000a6681dd9524800129b07ba2a4900024b613735492000437436e2a92400092d841c1524800129b06382a490002596047054920005b0c08e0a92400086c865d542480010d90cbaa64900029960875d85200052ac1ea9b0a4000a3584d4f61480014cf02a90c2900029960a75185200052ac1ea830a4000a6582d50614800192ae8b98c2900028d613531852000532c16a630a400087587d4861480014cf0ea90c29000299e115218520007133a2a430a4000e257454861480014cf06a90c290003919cd521852000722b9aa430a4000a648054861480014cb0b210c290002b160e421852000532c2a8430a4000a65858c8614800154b09190c29000299615321852000638baae030a4000cb1745c061480019a2e6b80c29000398549701852000632b90c3a8a4000c657518721480014c90ca8e4290003199d951c852000632ba8c290a400087787d84504800186ae9b08a090003155cf611412000632b96c2282400087587184504800186ae8308a090003155cc611412000632b90c22824000c677518620480010bb07ba2ca100020f61373594200042ec1ceb3204000a1d839d6640800143b073aac8100021760f76d50200042fc32e7aa04000c1e645cf540800183ac8b9ea8100020f6127598c200050ec24eb318400085d87d52630800143b093aac6100021761f5458c200041ec26eda98400083f865d3530800107b0f326a6100020f61d64d4c200060eba4c7a984000c1d7458f530800186cc8b8ea4100030d59171d48200062b31ae3a904000c55635c752080014ab07aa4c2100028d61353984200052ac1ea8b084000a3584d4d61080010eb0fa92c2100030b99172d442000616b22e5a884000c4e635cb510800189ac6b96a210003195ca61d442000632b92c3a88400086d86dc9510800185
  | 3 => 0x2a9a600091d841c1534c001838c8382a698002536087054d30004aac08e0a9a6000b19841c1534c00183aea3248698002872195490d300060f3b2a921a600085c865d5434c00183aea32286980021d60476d49300060e322e7a926000c37645c7524c001868c8b8ea498003075d464cc9300064a322e39926000c1d75191324c0010db043b6a2980030719173d453000617b22e5a8a6000c2c645cb514c00183aea32662980032319172cc5300060eba8c898a600083f87d90504c00107b0e320a09800307d9173141300060e322e62826000c2f645c8504c001858c8b90a0980030dd9171141300061a322e22826000b1b8454e404c001c30c8a9c8098002a6a1a43901300061c3b2a8a026000c587654d404c001930eca1a8098002c661543501300060fba8c9182600083d84dcd650c0010eb03b92ca180021b60b71594300060eba8e6b20600085d835db540c00183cc8b9ea8180030759173d50300042ec36e6aa06000c1d64dcd540c00107b093acc6180020f61e64d4c300041ec3ac9a986000a1d86550430c00183aecaa08618003165957010c300064cb22e02186000d19545c0430c0010eb033acc41800299606759883000526c1ea93106000a2d84d4e620c0014cb033aac4180029360f545883000527c1aa8b106000a2d84d4d620c001c1aa821ac418002b260043588300043ac0eeda906000877865c7520c00186cc8b8ea4180030d59171d483000633312e3a906000c65625c7520c0010db053acc2180029960a75984300052ac1ea93086000a3584d4e610c0010eb0fa94c2180029960a75584300052ac1ea8b086000a5783551610c00146b09a9ac21800385550435843000568c0086b08600087587d49610c0010db05bb6a2180021be1972d443000617322e5a886000c2d645cb510c0010db0f316a2180021b61d62d443000632b94c3a886000c6572587510c0010bf0cb9ca01800307591739403000626b9ac52806000c5573586500c00107b09bb0a0180020fe1974140300041ec3cc8280600083d87590500c00183cc8b98a01800307591731403000437c32e42806000c2e645c8500c00185ac8b90a0180021b61e621403000616ba4c42806000c4d73988500c00185ae8b10a018003135cd62140300043bc32e22806000c36645c4500c00186ac8b88a01800319989711403000632b12e2280600087587984500c00186ae9308a018003155ce611403000632b94c22806000c3574584500c0018aae6b08a018003195c961140300060eb28e8980600089c87591300c001918e8b126018003251d1614c03000633392e332e400085d83dd165c800107b09b9acb900021760f76d53200043ac0eedaa6400087581dd954c800107b09bb6a7900021d60776d4f200043ac0eeca9e4000a668199552c80012cb03bb2a59000299a0
  | 4 => 0x11000146b09a9cc2200021d61f529844000532c14eab088000a5583d51611000146b09a9ac2200028de1153584400070aa9886b088000ab18010d61100010eb0fa92c2200021b60b76d444000437c32e5a888000c4e635cb511000189ac6b96a2200021b61e62d444000436c3ac5a888000c657298751100018cae4b0ea2200020fe1974940400060eba2c72808000c2d7458a501000186ae8b0ca02000217e1973140400042ec3cc62808000c1d7498c501000183ae8b18a0200021be1972140400062731ae42808000c4d635c850100010db0f310a0200030b5d2621404000626b9cc42808000c2d74588501000189ae6b10a0200021de1971140400062b31ae22808000c55635c450100018ccc4b88a0200031958971140400043ac3cc22808000c357498450100018aae7308a020003195ca61140400061aba2c22808000c557358450100018cae4b08a0200030759473500400064639ac4a008000c9473585401000183ae939ccb980021d607725973000436c16e2b2e6000a1e8499553cc00123b09bb2a79800287a137654f300042f43cc8a9e600095581dc953cc00129b05b8aa798002476107054f30004a6c10e0a9e6000955811c153cc00183aea32287980020f61376d4b300043ac0eeda96600083d84dd952cc00107b09bb6a3980021b60b76d47300041ec26eca8e6000a1c845cf658c0010ef02b96cb180021be0971d96300060f3a2e632c6000c1d745cc658c00185ae9390cb18003135ce7219630006173a2e432c6000c2d745c8658c00189ae6b90cb180030d5d271196300062ab9ce232c6000c65729c4658c00186ce8b88cb180030d5d171196300062ab9ae232c6000c66725c4658c0018cae4b88cb180021b60876d52300043ac08edaa4600086d821d9548c0010eb023b2a9180024e6107054e300042ec3eca21c6000a1e86550438c0018b6cab80871800326d917010e300068caa2e021c6000875819d6628c00107b083b2a5180021d6047654a300053240ac4a94600086d829d6618c00107b083b2a3180021b608765463000532412c2a8c6000b1b83551408c001a32a839a811800266a1f43502300042fc1ae9b2a6000877815cb654c0010df04b8eca980028760c75d91300050ec1cea3226000ca5725c4644c001872eab80c898003265cd701913000654b92e03226000cb1715c0644c0010b90cb9ea89800307d9173d51300060e322e7aa2600083c865d3534c00107f0fb26a6980020f61c64d4d300049cc20e0a9a6000a1e84dd9534c0010bd0dba2a69800217a1e6454d300050f424c8a9a6000c1f74191534c00183d0e322a6980030761c6454d3000707410c8a9a6000e0d82191534c001c2d02322a698003856046454d300070cc00c8a9a6000c1c64dc9534c0012ab03b92a698003071937154d30004a6c16e
  | 5 => 0x80035848570084500070cb22c7300a000e6162586601400183ce8b9ccba00021d607725974000436c16e2b2e8000a1e8399554d000123b07bb2a9a000287a0f76553400049ac0ee4aa6800092d82dc554d000123b06382a9a00024b60870553400049ac08e0aa6800085d83ddb52d00010eb03bb6a5a00021760f7654b400042ec1eeda8e800086d82ddb51d00010bb07bb2a3a00028720d74d96400043bc0ae5b2c800086f825c7659000183ae9398cb20003075d1731964000616ba4e432c8000c4d739c8659000185ae8b90cb20003139cd721964000626b9ae432c8000c35749c465900018aae7388cb20003195ca71196400061aba2e232c8000c56735c465900018aae6b88cb20003199c9711964000632b92e232c8000959831c154900010db043b2a7200021d6047654e400041ec3eca21c8000c3b655c04390001a32a6b8087200021d6067598a400042ec18eca948000875811d952900014c902b12a5200021b60a75986400042ec18eca8c800086d821d951900014c904b0aa3200021de0572d954000437c12e3b2a800085c865cf54500012b306382a8a000287a0f76551400041f436e6aa2800093581dc9545000125b05b8aa8a00024760c705514000496c10e0aa28000935811c1545000163306382a8a00028761075d8d400050fc1aa831a8000a1d849d463500010bb0faa0c6a000287e1d5418d400050fc12a831a8000a1f81550635000143900aa0c6a0003835527218d4000706aa2e431a8000e15549c46350001c2aa8b88c6a0003315c97118d400062cbaae031a8000e19545c06350001992e4b80c6a0003345c57018d400060eba6c7a9a8000c1d7418f535000183aea31e86a00028721953d0d400060f3b2a7a1a8000c1d7518d43500010eb023b6a4a0003075d063d49400062bb1ae3a928000c54635c7525000183aea31e84a00032518d71d09400060eba8c6a12800086d821db515000183ae831ea2a000313d8d72d45400062631ae5a8a8000c1d7518f4150001918c6b9682a0003075d463505400042fc3ec62828000c1d74d8c50500010bb0e318a0a0003075d0631414000627b1ae42828000c4c635c850500018aec6b88a0a00031518d71141400060fba8c7202800087581dc965100010db05b8aca200021761f5458c400060eba4c7a988000c1d7458f531000107b0dba2a62000307dd16354c400050ec32a62188000c39655c04310001a32a6b8086200021d606759884000532c0ceb3108000a4d83d52621000145b09a9cc42000299606755884000526c1ea8b108000a2d84d4d621000145f08a9ac4200038354c435884000554c0086b10800087581ddb52100010ef0cb8ea4200031598d71d48400062ab1ae3a908000c66625c752100018cac4b8ea4200021b60a759844000532c14eb3088000a5583d526
  | 6 => 0x51ac26e6b08a000a66829cd61140014cb0539ac2280021da1c43584500043ac3886b08a000e154310d61140014cd0421ac2280029960843584500053940086b08a000a718010d611400146d08392c2280028d61072584500052b418e4b08a000a55831c961140018cae4392c2280029ca0072584500043b43e84b08a00087587d0961140014ad07212c2280029560e42584500043b43e64b08a00087587cc9611400146d09192c2280028d61232584500051b420e0b08a000a35841c161140014ad06382c2280029560c705845000533410e0b08a000a65821c1611400107f0eb20c2280030759273184500060eb22e6308a00085f8758c611400183ce8b18c228003075d1631845000616b24e4308a000c4d639c8611400185ac8b90c2280031358d721845000437c3ac4308a000c2e74588611400185ae8b10c228003139cd621845000626b9ac4308a000c35649c461140018aac7388c2280031958a71184500061b3a2c2308a000c357458461140018ace6b08c228003155cd611845000633392c2308a000c657258461140018d2c5380c2280021760e76d045000436c14eda08a00086d869cb411400185ac939682280031358e72d045000616b22e5a08a000c4d635cb41140010df0eb1682280021b61d62d045000633392c3a08a000c657258741140010bb073b482280021b60a76904500042ec34e7208a000c1d649ce411400183ac8b9c822800217e1d63904500042ec3ac7208a000c4e7358a411400189ae6b148228003159cd61904500062ab9ac3208a00085d839d841140010db053b082280020f61276cc45000436c14ed988a00086d869cb311400185ac939662280031358e72cc45000616b22e5988a000c4d635cb31140010df0eb1662280021b61d62cc45000633392c3988a000c6572587311400107b093b462280021b60a768c4500041ec34e9188a00083f87592311400107b0eb246228003079d1638c4500060eba2c7188a000c2e7458a311400185ae8b1462280030d9d1618c4500061aba2c3188a00083d849d831140010db053b062280020f61276c84500042ec1ced908a00083d849da21140010bb073b442280020f61276084500042ec1cec108a00083d869d0211400107f0eb2042280020f61d64084500042ec34e6108a000c1d649cc211400183ac8b98422800217e1d63084500042ec3ac6108a000c1e7458c211400183ae8b1842280030b9d1620845000616ba2c4108a000c4e73588211400189ae6b1042280030d9d161084500061aba2c2108a000c567358421140018aae6b08422800299619210845000632bb242108a000e25644842114001c8ac690842280030e59270084500062cb1ce0108a000c69629c021140018e2c338042280030e59170084500062cb1ae0108a000c69625c021140018e2c2b80422
  | 7 => 0x1d7458c621400185ac9390c4280031358e7218850006173a2c4310a000c2d74588621400189ce6b10c428003135cd62188500061ab24e2310a000c55639c462140018cac5388c4280030d59171188500062ab1ae2310a000c65625c462140010bb073b684280021d60676d08500043ac34e3a10a000c35649c742140018aac738e84280031958a71d08500061ab22e3a10a000c55635c742140018cac4b8e84280021760e76908500043ac0ced210a00085d869ce421400183ac939c84280030759173908500042fc3ac7210a00085d8758e421400189ce6b148428003135cd62908500042ec1cec210a000875819d8421400107b093b664280021d60676cc8500043ac34e3990a000c35649c732140018aac738e64280031958a71cc8500061ab22e3990a000c55635c732140018cac4b8e64280020f612768c8500043ac0ced190a00083d869d2321400107f0eb2464280020f61d648c8500060f3a2c7190a000c1d7458e321400185ce8b1464280030b5d1628c8500041ec24ec190a000875819d8321400183ac939ec2280030799173d84500060eb22e7b08a000c1d7498f611400183ce8b1ec228003075d163d845000616b24e5b08a000c4d639cb611400185cc8b96c2280030b59172d84500062731ae5b08a000c4d635cb611400185ae9316c228003135ce62d8450006173a2c5b08a000c2d7458b611400189ce6b16c228003135cd62d84500052ac1ec9308a000a6582d92611400146b09b1cc2280029960b63984500070ab24c7308a000e166458e6114001c2ac8b1cc2280028d61362984500052ac1ec5308a000e256498a6114001c8ac7314c22800389991629845000712b22c5308a000e466358a6114001c8ac6b14c2280021760f74584500041ec26e6b08a000a5683d9161140014ab07b22c22800299a0b645845000532c16c8b08a000a358699161140010ed0e322c2280028da1064584500052b418c8b08a000a558319161140014cd04322c2280029960864584500051b426c6b08a000a3584d8d61140014cd05b1ac2280029960b63584500052ac34c6b08a000e166498d6114001c2ac931ac2280038599163584500070ab22c6b08a0008768718d611400146d0831ac2280028d61063584500052b418c6b08a000a668218d61140014cb0431ac2280028da1362584500051ac26c4b08a000a5683d8961140014ab07b12c2280029961a625845000713324c4b08a000e25649896114001c8cc7312c2280039158e625845000713322c4b08a000e25645896114001c8cc6b12c2280039158d62584500043b438c4b08a000a3684189611400146b08312c22800295a0c62584500052ac18c4b08a000a668218961140014e500312c22800295a0f74584500052ac1ee8b08a000a66829d161140014cb053a2c2280028da1373584500
  | 8 => 0x2322c628002956046458c500052d400c8b18a000c1d741d1631400149d043a2c628002936087458c500052b408e8b18a000a55811d163140014b5003a2c62800295a077258c500052ac0ee4b18a000a1e849c9631400143b09392c62800293a0b7158c5000526c16e2b18a000a1e849c5631400143b0938ac62800287a107058c500050ec20e0b18a000a4e821c1631400149b04382c62800295a047058c500052ac08e0b18a00083f87590631400183ac9398c62800217e1d6318c500060f3a2c6318a000c1d7458c631400185ac9390c6280031358e7218c5000616b22e4318a000c4d635c8631400186ac9388c6280031558e7118c500061ab22e2318a000c55635c46314001872c9380c6280021b60a76d0c500043ac0ceda18a00086d829da43140010eb033b486280021b60a7610c500043ac0cec218a000a1d8650c431400183aeca1886280021b61a7210c5000616b24e4218a000c4d639c8431400185ac8b9086280031358d7210c500043ac34e2218a000c35649c443140018aac738886280030d5917110c500062ab1ae2218a000c39649c043140018b2c738086280030e5917010c500062cb1ae0218a000d19435c0431400183ac939ec4280030799173d88500060eb22e7b10a000c1d7498f621400183ce8b1ec428003075d163d88500061ab24e3b10a000c55639c7621400186cc8b8ec4280030d59171d88500062b31ae3b10a000c55635c7621400149b07b24c42800299607649885000516c26c7310a000a6581d8e6214001c1ac931cc42800383991639885000706b22c7310a00085d83dd1621400107b09b9ac42800293a0f645885000526c1ec8b10a000a6681d9162140014cb03b22c4280028b61a645885000437438c8b10a000a2e84191621400149d06322c4280029360c645885000533408c8b10a000a6581191621400145d09b1ac4280028b61363588500053340ec6b10a000a6581d8d621400149b0d31ac42800383992635885000706b24c6b10a000e0e6458d6214001c1ac8b1ac4280021ba1c635885000517420c6b10a000a2d8418d621400149d0631ac42800299a04635885000532c08c6b10a000a4e83dd1621400149b07ba2c42800299a06745885000532c0ce8b10a000a2e84dcd621400145b09b9ac42800299a06735885000532c0ce6b10a00086e8710d62140010db0e21ac4280038350c43588500053340886b10a000a658110d62140014d50021ac4280029a600435885000517420e2b10a000a2d841c5621400149d0638ac4280029360c715885000632b88e2b10a000a6a801c5621400145d08382c4280028b610705885000527418e0b10a000a4d831c162140014cd02382c4280029960470588500041fc3ac8310a000c1d649cc621400183ac8b98c42800217e1d63188500060f3a2c6310a000c
  | 9 => 0x215802100731a9a42b004200e6153485600840143906b22a928002872116354e500053240ac4a94a000a6482585519400107f0eb20c92800307591731925000616b22e4324a000c35645c464940010bf0eb18c728003075d16318e5000626b1ae431ca000c55635c4639400183aeca1887280034650d7010e500061ab22e3a14a000c4d7358a42940010bf06bb285280021de057650a500062ab1ae3994a000c2d7458a329400107f08bb265280021de05764ca5000616b22e5a0ca000c557358641940010bf06bb283280021be09765065000626b1ae598ca000c3574586319400107f08bb263280021be09764c65000632bb24210ca000d61215c0219400143d073aac8280028760e75590500042ec34e7aa0a000c1d649cf541400183cc8b9ea8280030759173d50500042ec3ea9318a000a1e849d5631400143b093aac6280020f61a74d4c500041ec3cc9a98a000c1d7498f531400183ce8b1ea628003075d163d4c5000526c1ea9310a000a2d84d4e62140014cd033aac4280029960675588500052741ea8b10a000a4d83d51621400145d09a9ac4280028b61353588500043ac34e3a90a000c35649c752140018aac738ea4280031958a71d48500061b322e3a90a000c35645c752140018acc6b8ea4280031558d71d485000632b12e3a90a000a5583d52611400146b09a9cc2280021d61f529845000533414eab08a000a65829d561140014ad07aa2c2280029560f54584500051b426a6b08a000a3584d4d61140010db0d396a2280030b59272d445000626b1ce5a88a000c2e645cb511400185ac8b96a2280031398d72d445000626b1ae5a88a00086d8798b51140018cce4b0ea228003195c961d44500050ec1ec9320a000a2d82d92641400146b03b24c8280021d607725905000436c16e2b20a000c1d731cd641400145d0439ac8280028b60873590500051b408e6b20a000a35811cd64140014750039ac8280028da0772590500051ac0ee4b20a000a1e839c9641400143b07392c8280028ba0b715905000516c16e2b20a000a1e839c5641400143b0738ac82800287a0c70590500050ec18e0b20a000a2e821c1641400145b04382c8280028da0470590500051ac08e0b20a00083f87590641400183ac9398c82800307591731905000616b24e4320a000c2d645c8641400186ac9388c8280030d591711905000616b24e5b18a000c2e645cb631400185ac8b96c6280030d59271d8c500061b322e3b18a000c35645c7631400143b09b1cc6280029360b6398c500052ac0ec7318a000a4d82d9263140014ab03b24c6280021d6077258c5000436c16e2b18a000a4e82d91631400149b05b22c62800295a076458c500052ac0ec8b18a000a1d8699163140010bd0e322c62800287a106458c5000527410c8b18a000a4d8219163140014ad
  | 10 => 0xa0842009658754a3108401a4ae8a946210803a1591324c42100437c32ea9084200877865d521084012cb0bbb242108029961a754842100533c32ea9084200967865d521084018cf0cbaa421080259e117548421004b3c1aea9084200964805d521084012cb0eb2a4210802596177448421004e2c1ee89084200d25759912108401a4aeab2242108025961f5448421005a2c1ea890842009658755121084012cb0bb9a4210802696137348421006a2bacc69084200d457558d2108401d0ac8b1a42108025961f534842100592c26a690842009658754d21084012cb0a3824210802696107048421004e2c18e09084200b61854866008401473083acc0108029660c75980210052cc1ea93004200a3984d4e60084014e303a94c0108029a60b51980210041ec20eab00420085d831d560084014d100a92c0108029c201515802100532c2a42b004200ae08048560084014d70ca92c0108038a991525802100714b22a4b004200e4a635496008401c92c6a92c0108029ce19515802100719322a2b004200e31645456008401ca4c6a8ac0108039458d5158021005b0c2a42b004200e62654856008401cc2ca90ac010803a8991215802100750b2242b004200ec2634856008401d82c690ac0108028e61075580210052cc18eab004200a5983d5160084014d305aa2c0108029c60754580210051cc26a6b004200a6982d4d60084014e303a9ac0108029c607525802100570c0ca4b004200a688754960084014d708a92c0108029ae0d525802100535c0aa4b004200e62815496008401cc302a92c0108029a616425802100564c1c84b004200ae18190960084014d30aa12c0108029a616325802100554c2464b004200ae1818c960084014d30a992c0108029a60b515802100570c14a2b004200e61529456008401cc4a4a8ac0108039854951580210053843aa2b004200a738454560084014e706a8ac0108029ce09515802100731412a2b004200e61825456008401cc484a8ac01080398509515802100731192a2b004200e613254560084014e30b20ac010802b460e415802100570c1482b004200e615290560084014e30aa0ac01080398549415802100750a1282b004200a71858c560084015630918ac010802b860a315802100730a9462b004200a71854c56008401cc2a498ac010803b04c9315802100534c2e42b004200e6151c8560084014e30b10ac0108039854a215802100534c2a42b004200e63514856008401cc2a290ac0108029c615215802100731a9242b004200e615248560084015c10e90ac010802b8e1521580210073142a42b004200ae1854856008401cc30a90ac01080298615215802100731baa42b004200e607548560084015c70890ac010802b8611215802100731aa242b004200e615448560084015c70690ac010802b860d
  | 11 => 0x8c4010db04382cb188028760e75992310050ec1ceab246200c1e645cf548c40183ac8b9ea9188020fe1974d4e310041ec3cc9a9c6200c36645c7528c40186ac8b8ea5188030d5937154a3100617322e5a8c6200c2d645cb518c40107b083aac118803079d1739953100616ba4e532a6200c2e745ca654c40185ae8b94ca98803155cd719953100633392e332a620083d84dcd654c40143d09b9aca9880299a0b71595310041ec20e0b2a620086d821c1654c4010bb07bb6a8988021b60b76d513100436c16ecaa2620085f87597434c40143b0caa08698803165957010d310064cb22e021a6200d19545c0434c40107b09bb2a4988020f6137654531005c2c1086a0a6200b918010d414c40107b093aec0988021b60a75d81310041ec20e0b28620086d821c1650c4010bb07ba2cb908020f61373597210041ec20e0b2e420085d831c165c84010bb07bb6a9908020f61376d4f21004aac1ee8a8e420093584dcd51c84010eb0c382a3908024d6107054721004aac18e0a8e4200965821c151c84010bb07ba2cb108020f61373596210041ec20e0b2c420085d831c165884010bb07bb6a9108020f61376d4e21004a6c1ee8a94420092d84dcd52884010db0c382a5108024b6107054a21004a6c18e0a944200965811c152884010bb07ba2ca908020f61373595210041ec20e0b2a420085d831c165484010bb07bb6a8908021b60b76d51210043ac0eedaa2420086d82dd954484010eb03bb2a8908020f61376d4d2100436c16eda9a420087581ddb53484010db05bb2a6908021d6077654d210042ec1ee8b28420083d84dcd650840107b08382ca108021760c70594210042ec1ceb3204200a1d839d6640840143b073aac8108021760f76d50210042fc32e7aa04200c1e645cf540840183ac8b9ea8108030b59172d50210061ab22e3aa0420083d849d6630840143b093acc6108021761f5498c210050ec24eab18420085d87d51630840107b09bb6a6108020fe1974d4c210041ec3cc9a98420083d87593530840183ae931ea610803075d163d4c2100626b1ae5a984200c55635c7530840186cc8b8ea4108030d59171d48210062b31ae3a904200c55635c7520840129b07ba2a41080259607745482100496c26e6a90420096581dcd5208401c1ac8b1aa41080299e19715482100496c20e0a90420094d831c152084012cb02382a4108030b99172d442100616b22e5a884200c4e635cb510840189ac6b96a210803195d95294421004aac1ee8a88420096582dd1510840126b09b9aa2108025960b73544210070ab22c6a884200a65869c951084014cf0cb92a2108025961e4254421005a2c1c84a884200965878c9510840164b09192a2108024d6107054421004aac18e0a884200965821c151084012cb0ea948210803515cd529042100742b1a84
  | 12 => 0x8021760f7458b510041ec26e6b16a20083d841c162d44010bb06382c5a880293a0f6458b5100526c1ec8b16a20086e8719162d440145d09b1ac5a88028b6136358b5100437438c6b16a200a4e83dd162d440149b07ba2c5a8802996067458b5100517426e6b16a200a2d84dcd62d44014cb0339ac5a88021ba1c4358b5100436c3886b16a200e0d4310d62d44014cd0221ac5a8802996044358b510053540086b16a200a698010d62d44014cf02b82c5a88028ba107058b5100516c20e0b16a200a4e831c162d440149b06382c5a8802996047058b5100632b14e3a16a200c65625c742d440189ce6b1485a8803135cd6290b5100632b14e3996a200c65625c732d440185ce8b1465a88030b5d1628cb510042fc1ae9306a20083f845ce60d44010db0f310c1a88030b5d2621835100626b9cc4306a200c2e7458860d440185ae8b10c1a8803139cd621835100626b9ac4306a200a1e83d91545440143d09b1aa6a880259a0b7159151004b3416e2b1aa200d19435c0435440189ae7b1484a88021760e765095100616ba6c5192a20083d849d9325440183ae9398c0a8803079d173181510060eba2e6302a200c2d749c8605440189ae7390c0a88030b9d1721815100616ba2e4302a200c4e735c8605440189ae6b90c0a880319e0572181510063240ae4302a20085d831c165d04010db04382cba0802876195310f410061cb2ae021e8200c99635c043d0401a32a6b8087a0802996067598b4100526c1ea93168200a2d84d4e62d04014cb033aac5a08029360f5458b4100516c26a6b168200a2f8454d62d0401c1aa621ac5a0802aa6004358b4100633312e3a968200c65625c752d04010df0cb96a3a08021b61e62d474100436c10eab06820085d831c165904010db04382cb2080217e1973d52410050ec24eb31c820085d87d52639040143b093aac720803075d263d4e410060eba2c7a9c8200c56635c752904018aac6b8ea5208031558f7154a410062731ae5a8c8200c4d635cb51904010bb063aac120803075d2739954100626b9ce532a8200c4e735ca655040189ae6b94caa08030d5d1719954100633392e332a8200a1e83dd165504014cd05b8acaa08021760c705954100436c10e0b2a820086d82dd95350401872cab8086a08034654d7010d410042ec1eeca92820085d839d760504010db053aec0a08021760c705944100436c10e0b28820083d841c165cc4010db04382cb98802876195410f310062cb2ae021e6200c99645c043cc401a32a8b808798802996067598b3100526c1ea93166200a2d84d4e62cc4014cb033aac5988029360f5458b3100527c1aa8b166200a2d84d4d62cc401c1aa821ac598802b26004358b3100633312e3a966200c65625c752cc4010df0cb96a3988021b61e62d473100436c10eab06620083d841c165
  | 13 => 0x68ca1ae021aa400c1d749cc605480183ce8b98c0a9003075d173181520061aba4e2302a400c55739c4605480186ce8b88c0a90030d5d171181520062b39ae2302a400c55735c460548018cf04b88c0a90031920971181520042ec18e0b2e8400875811c165d080143b0ca9887a10030e5957010f420064cb1ae021e8400d19535c043d08010ef0cb8ea5a10029960a75987420052ac1ea930e8400a3584d4e61d08010eb0fa94c3a10029960a75587420052ac1ea8b0e8400a3584d4d61d080146f08a9ac3a10038554c435874200558c0086b0e8400875811d560d08010bb06382cb210021d60470596420042fc32e7aa48400a1d849d663908010bb0faa4c721002876127558e420060eba4c7a9c8400c1d7458f53908018acc6b8ea5210031558d71d4a420042ec18eab048400c1d749ce655080185ae8b94caa1003155ce719954200632b94e332a8400c56735c665508018aae6b8ccaa100287a0f74595420053340ee4b2a840085d831c165508010eb02382caa10021d6077654d420061cb2ae021a8400d19535c043508010bb073aec0a10021d60675d81420042ec18e0b288400875811c1651080107b08382cb990021d60470597320050ec32a821e6400c59655c043cc801932c8b808799003465517010f320043bc32e3a966400a65829d661cc8014ab07aa4c3990028d61353987320043ac3ea530e6400a65829d561cc8014ab07aa2c39900295e0d54587320051ac26a6b0e6400e155410d61cc8015a30021ac3990021d60475583320041ec20e0b2c6400875811c1658c80143b073acc9190028760e75592320060f322e7aa46400c1d645cf548c80107f0cba6a7190020f61e64d4e320061b322e3a946400c35645c7528c80107b083aac119003079d1739953200626b9ae532a6400c35749c6654c8018cae538cca990030d9d171995320061aba2e332a640083d84dcd654c80143d09b9aca9900299a0772595320041ec20e0b2a6400875811c1654c8010bb07bb6a8990021d60776d51320043ac0eecaa2640085f87597434c80143b0caa08699003165957010d320064cb22e021a6400d19545c0434c80107b09bb2a499002e16044350932005c4c0086a12640083d849d7604c8010eb033aec0990020f61070594320043ac08e0b286400c1d649cf54d440183ce8b1ea7a88029360f5498b5100516c26a7316a200a4e83d5162d440149b07aa2c5a88028ba135358b5100516c26a6b16a20085d831c164d44010db04382c9a88020f6107058f5100436c10e0b1ea20086d829db43d44010db053b487a88021b60a7610f510050ec328621ea20086d869c843d440186ac8b8887a88031558d7110f510061cb22e021ea200c59635c043d4401a3286b8087a88029360f6498b5100532c0ec9316a200a2d84d8e62d44014cb03b1cc5a8
  | 14 => 0x583d516110c0146b09a9ac221802c6615439804300534c10eb3008600a71811d66010c014b307aa4c0218028e613539804300436c10eab008600875811d56010c0147100aa2c0218029620153580430050ec2a86b008600a988050d6010c014770caa2c02180296e1953580430058cc2a86b008600e1a6550d6010c01c32caa1ac0218038a552625804300724a9cc4b008600e89439896010c01c52a8b12c0218039254d625804300744a1ac4b008600e31549856010c01ca2a730ac021803a450e615804300718aa2c2b008600e51535856010c01d2286b0ac0218029a608755804300538c08eab008600a5983d516010c01533072a2c0218028e21d54580430051dc1aa8b008600e1a835516010c01c3306aa2c0218028ee0954580430051dc0aa8b008600a3984d4d6010c015330929ac0218038655253580430070d2a2a6b008600e195454d6010c014b10ea9ac02180296e1153580430070d422a6b008600e198454d6010c014b704a9ac02180296e0553580430051cc2e86b008600e1953d0d6010c014b30b21ac0218038655243580430051cc2a86b008600e1b5350d6010c01c32a6a1ac0218029661543580430070daa286b008600e195450d6010c015310ea1ac021802a6e1543580430070d42a86b008600a998550d6010c01c330aa1ac0218028661543580430070dbaa86b008600e187550d6010c0153704a1ac021802a6e0543580430060eb24e7aa6a400c1e7458f53d48014ab07aa4c3a90028d61353987520052b41ea8b0ea400a5583d5161d480146d09a9ac3a90028d61353587520042ec18e0b26a400875811c164d480107b08382c7a90021d6047058f520043ac0ceda1ea400875819da43d48010eb033b087a9002876194310f5200616b22e421ea400c4d635c843d48010eb0d38887a90030e5917010f520062cb1ae021ea400d19435c043d48014ab07b24c3a90029960b64987520051ac26c730ea400a6582d8e61d48010bb07ba2c3a90020f61373587520041ec20e0b0ea40085d831c161d48014ad07b22c3a90029560f64587520043b438c8b0ea400a3684d8d61d480146b09b1ac3a90021da1c63587520052b41ee8b0ea400a5583dd161d48014cb053a2c3a90028da1373587520051ac26e6b0ea400a65829cd61d48010ed0e21ac3a90021d61c43587520070aa1886b0ea400a668210d61d48014cb0421ac3a90029ca00435875200538c0086b0ea400a67825c161d480146d08382c3a90028d61070587520052b418e0b0ea400a55831c161d48014cb04382c3a900217e0d74983520041fc22e7306a4008758798460d480186ae9308c1a9003155ce61183520061b3a2c2306a400c357458460d48018ace6b08c1a9003155cd61183520050f41ec8aa2a400a1e84d8d53548012cd03b92c8a900259a077258d5200
  | 15 => 0x3b92c9a98021b60b715935300436c10e0b26a600875811c164d4c0146d03b92c9a98028d60772593530050ec1ce4b26a600a2e82dc564d4c0145b05b8ac9a98028760e71593530050fc1ae0b26a600a1d831c164d4c0145d04382c9a98028b60870593530051b408e0b26a600a35811c164d4c0107f0eb20c9a98030d59271d8b530061b322e3b16a600c35645c762d4c0107b08382c5a98021d6047058b530041fc3ac8316a600c2d649cb61d4c0185cc8b96c3a98030b59172d87530041ec20e0b0ea60086d821c161d4c0107f0eb20c3a98021de05729835300437c12e3306a60083d8799060d4c0185ac9390c1a98030b991721835300616b22e4306a600c35649c460d4c0186cc8b88c1a98030d59171183530060ebb4e9a9ca60083f875906454c0183f06ba0c0a98030720d741815300616ba4e4302a600c2e745c86054c0185ae8b90c0a98030d5d2711815300632b94e2302a600c36745c46054c0186ae8b88c0a9803199c9711815300632b92e2302a60087581dc965d0c010db05b8acba18021b60870597430043ac08e0b2e860095581dc953d0c0129b05b8aa7a1802176187054f430048ec20e0a9e860094d821c153d0c012ab02382a7a18021d607725964300436c16e2b2c860086d821c16590c010eb02382cb218024d607725524300496c16e2aa4860083d861c15490c0123b06382a9218024b60870552430049ac08e0aa48600c1d745ce6550c010eb03b92caa18021b60b715954300436c10e0b2a8600875811c16550c010eb03b92ca218021b60b715944300436c10e0b288600875811c16510c0143f0cb9aa8218024760f72550430049ac0ee4aa0860091d83dc55410c0125b05b8aa8218024760c705504300496c10e0aa08600935811c15410c0183aecaa4a6218028761a7454c430050fc32e8a98860091d84dc95310c012ab03b92a621802476137154c43004a6c16e2a98860091d841c15310c0129b04382a621802556047054c430041fc32eaa188600c1f7654d4310c010bf0cbaa862180307dd95450c430048ec2eeca188600a1d869d54310c0143f0cbaa862180307dd97550c430048fc32eaa188600c1f865d54310c0123f04baa862180247e057550c430048e402eaa18860091d875954310c0183eecb2a8621802476177250c43004cac0ee4a18860091d85dc54310c0131b05b8a8621802476147050c43004c6c10e0a188600995811c14310c010eb033acc421802c3615439884300532c0ceb3108600a4d83d526210c0145b09a9cc421802c3615435884300532c0ceab108600a4d83d516210c0145b09a9ac4218021b60a75984430058ac2a873088600a65829d66110c014ab07aa4c2218028d61353984430058ac2a86b088600e25545896110c01c8aa6b12c221803a150d625844300532c14eab088600a5
  | 16 => 0xe00000400000400c00000202003600200201000200004601a00a00000403a00200200000000e00a00800200000201a03400200000e00800200000600000000000601000800401c00600604000200c00400400000400000000201200000800200000800a00000000200001000400202200001600600600400001400000801000000000400202000000000002004200800400c00001a00000000801000200c00c00200000800400000201e00800000200200601a00000003000001600201202600200400000400000600800600001600000000200603600000000400001001600000a00c01802600000a00000400803c00c00a00000000e00200a00200000800800000000000200000000001000200200a01600400800001600600600000c01000800402a00801000000a00402000002400800a00600400200000200000c00600200200000001200200a00600a01001003402c00000000a00001000c00201a00600000200001600000000600000000001800400000200200e00000000200200000000c04000001204400200600000400400000205200000400000000000a02000400400600000400000400600200800400c00000200800400800000200400001200200002600600200600a00200200800001a00600000000000400601000200c00000204000000000200200200802200000600400200401e00000a02c01202000800e00800c00c00200000600800c00200800a00000000600200001000200000c00000000000400000800201200a00200600400000200000800201c00c00602400000800000600400200600200001004e00200000000200000400200400a00403000000000000002200201c01202800c00600200c0080087581dc963d50010db05b8ac7aa0021b6087058f540043ac08e0b1ea800a5681dc963d50014ab03b92c7aa002876127258f5400527416e2b1ea800a4d82dc563d500143b0938ac7aa00287e117058f540050ec20e0b1ea800a4e821c163d500149b04382c7aa00295a047058f540052ac08e0b1ea80085f8758c63d50018aac738ec5aa0031598d71d8b540062ab1ae3b16a80085d831c162d50010eb02382c5aa00217e1d6318b5400626b1ce5b0ea800c4e635cb61d500189ac6b96c3aa0021760c705875400436c10e0b0ea80085f8758c61d50010ef02b94c1aa0021be0971983540042ec3cc6306a800c4d639c860d500189cc6b90c1aa0031358d72183540062ab1ce2306a800c56635c460d50018aac6b88c1aa003075da73d52540042fc3ac631aa800c1f845cc605500183908b98c0aa003135ce72181540062739ae4302a800c4d735c860550018aae7388c0aa003195ca71181540062b39ae2302a800c55735c460550018cce4b88c0aa003195c971181540060eb24e7aa6a600a1d83d9264d4c010eb0
  | 17 => 0x8b0aacbc815919d03688b87453340000c5627401880000004752a0800000042f41d20240000d127a09acac800011b8000d3a6552e680010a80000c88d88fbc2ac0001bfcb5e0001430c7899a85746ca268f3600000016aca6c292180000073200038682e87fa7df0ad095c00006e134800000046b193800000064d15b80000006a933f8000bc64a927896606ec0002ad80003d46a00ea8c4400050200000002ac000228139800000000000000000001ed1d1868e0000a221410f68a64080bd883c1a22ac80003da3e530d06c467a0c417d04c8000000000000009a00022d199806600000000000000000000000f240003369a88e785870c4840c1942f501f1db80000000001e5841800000000000007994239e010048792770678ee46e534d1b08508717084136c57a72c3a4189853883245622ac38676544e9fb488c77800006dcb225a71170d50a9e000000000000088600010d0ec23e4000000070e24d00004682826874640b5c2740002b30000f724fb399a12916247932e00000007e33041ff07e412324c06d0e080ef00000000104a03110448b320004270c680008b90e51e290180702e614a05543d11b409f04688ba04b060070881a0a196b85600c8000000071600000000005783b82fb92e42660000000c6100e09826f18010826030678124bae18f29a19100000d025204e400000000685fcce20003b680000004012ed800001a01400400004400000000000a00200a00200201c00601401201200a00200600200000400c00800000200c00000600800400000800201400000400e00000400600000000200600400006000000000400000c01200001200000000000600800000800c01400200600001601a00e00001200200200201400200c00200600000200200200000000000200e01c00401801c00201a00800001800e00000400000c01001e00802a00000001800001200000200200600601a00600001e00e01000001400800600600000200200801e00001e00800c00002400e00001800a00400200e00000602400400200000000400001800600a00c00800a01e00000000000a00c00600002000200800a00002c00200002000000200200800000000400400000600e00c01000000a00200000400000000000a00c00000c00600800000e00000002400600400200002400200000200000201601601800000c01400400200a00200e00000000000000000200000c00a01c00a00c00200400a01200003600200800200c00200000000202201600001200000401201600000000800001400400600a01a00200e00600200800600201400200001c00a00002201200800c00000000400000204400201601a00a00000200000801200800000000400a00000200000000000000200a00a00203e00800c00603000400c01800600801c004040002
  | 18 => 0xbd200019692540000000000b600000003d0000000000000000005224850cf8bac0b23e700000000000000000000c8c00000000000002ae000081110a7d91be000008269f3659e9091663b035a00c17872916f1e4c1b200039f074800032f000143c90245612800010ce0000000d247880db2910790cb67312f813fc23c8010da8ef4d5e0e30d38000fd46372289ae884c6c1000000012221918296a4890000000103c04c09445a9700e724dd00614ecf1802700007a00002b90000e4cf8a03808080008064b61579fec00000015385d02fa5812620150bd67cb322a108000738225a02cb9c00e111a0610a48154491e7400073b159111000077300000007bc3363aa96900005b104e000d1b44a71d2000000024a0f30c0ce46165000000027e26409e80000004b20000000d086b3000233856c37f0a40000f441712001d4000021824018bce4a0c606298cc00018100012f85f08db0cc1bb80a20003b300a8dd20002cf972875681b000000014e24445b833800000000002ccc386293738cfce8606035a00005400000000cd117a87200000006140001ff00000001f608da1bc71e4f70409e9c00022a152000077244700001f800000009210340007d82889dd000000000000005a48a90002380a320443f480000ee00031f00000008ca0000000cce0000000d5c02288e0f0140c4628202709e181186e314b020842c7b106c05f10d286c2de9708e4089324f10acc403382528000faa3e931e8759048653000000043a00000014e89c834d3e0232cf12285302000000058b255915c81c405037950c7b6000241000065c3f400001d8e8200008380bc00023a0a100002d87e2000133c0000f900008207660003641e5c27c30b000000000000044a80005620950bf1d50f8e7d229300b4f46099093183c99800013c0000460000000000074c0000d184e08860e112616700aa0000868ad400087d14d80000002762ae1ff41a639c000006035e8781651d642180ab45913b4dd489f0ee00007a44d312015500003c13848000b6a1e1164a188d600002c693180000000cb8c641ca65e000065800011500000000001b6000121882874c0001fcd1185ec3af06943d87cf0000f181084d52ca856115042a0aa8dec7ae000035168476270032c80000c87520798ba400062500017747420000000000000000021946cfb883704680000000002740e300a400018a910000045e0000cf8d580000258fdcd6e2032961ed8a1c2db0df19f878e1c241b1a701c40000001c1ce2c0d725a8000a800b70888b64d8617b3d9154c2d634f2f71fdce9c256114000000018d183856c59c47f44e20b04403bb42c95dc00054b11118e4f68380455000082e00009513047786ef3a58a8868401041f0bb09e663c0020dacbd427946005244cc0c91288fd803472b18496f80005cb
  | 19 => 0x80000000966000424000034c78d38803a000000005c138839223c267084c53e00012c84b11102ea00014c44720000a601f03e46110159a382cc1b332f96d80000000c99b1c97e12700000000005fd011000000074035320284da0002d4000000064f28d1cb80001f1000000000042346f001d0f800038280000002cf00012bc000000000000000000000000006be0004639b340000000001fe0000454171800000052900000009ca0000b9800000000012f1a2c00075c0001ec000012b45b000000000000000000000000ed000000000010323187928290d413e400013b33900009ec37346c0000c260003b580009ae00007a2180ac628a2c8019886249f00000000000000001cd80000003e8a20400000000000000000a500017f8e300000578e7c6c621b1468edc00010a2cd12b08be18a0b79ac480c05a36600010fe1e300015a852615221090d800000000000000000000000c4c0001610b680000000000e08000e3c57435a93207fe0001aa8c5c2c031c28680700000bb0000df897821c000226c67228200019b8bd01861768000000035000089829467621d939cc5461038611d074e0003d2a0580006982d98e206642fc20e9e2ceee36d03da21000057a17c81006b60000ea00011a800a387011c3242211cd02b50ba6790d5800101a0000000640000000327000058c00033780000000003f8848400085e00016e40000001b7000000017700000011a03950dd0c98a945942ef9c880006230001fd508c00035b182800075604321d058e15037b8720fae4413ee9758a3a86628020b80b67c62129eb0b860002fc00010503ed1911f0cf3468645197404961bf007985ce4e1ce23b0c3c968341042924400052e2020000ba220022d830c00075324d80180004961ef868482c00023e9a9c000813269119cd9483411d80000004c200011841f420a00000011ba60700000002f200000009491980002a8800045e0003b387e85be5800000f8400000000009a0d883bf00008405fe0000000fe400000000011800002e60000000a4800000000000000001230000fdc270000083400000008f9538a6a6a111600000002b438e8d840d01bc44c00005e0689413000108800145080000004a10ab9cc002c1c60e6873c1680000000f4cf662ef3cc231497473a000000000079e00000003b0000000059029a26e00018b02404f51ae000003200016284b825e80806b00780002d12a314f800000028480000004aa2dd8db06ee00000017841aa4782b28d68838260000000000000000000000003902e3000061072400013ace6834800021cc0000000000e88000597000000000003c0001f34364000000209c0006f100000a00001cb00020b40001471a8000085a00023780000004e9000120c0000001698c480000000000b540000000000000000000000000
  | 20 => 0x28e3800000000000000b50001c6cdba3ad0001da80001143d0958840a0003f58a380ae0002b600000000d200000000008611a19d440002903de9a90efc0003b7979c0004fd0b401706785c400000010987aa24a000094c4713dc0dc4e1651604e8f885a08be000000000058821f09e80007761391f98a0c00010b971c0000003ad80009b410f22e80010aa00018f9c2070c214088195d1843d0000000043c182403121c6ea000000000021c6d108e8000000215000234c00076338191f031c02300580000001ac15c04dd0704ad00013f000000004f122800023d0f1000000000041180000003b5036000117879f000114c8d48a02cb00000008a526f800006800020898e00000000000000000000000167809e7191f58b74ad03ac3708000bf603f33b8a751681f50d703d400000012c0ca0fce00000011604ea0001961bb0cf400000000011a47830000000000000000000000049a0f80000da628732a0000ee032b35d871c6600000001d88000840000000000000000000000000003011fbcc3616303287403d20ae219882c8305d91398c80de84c33889a58e9200040c91e86ac523000210c0001f92a41770af60003a7800111447234693b00367d30001f0800042214080003062010ff8000d2a0000000a84f9c71200002a51c20000001c980e85f10780a5c00000043580000001340000000d3c0e003880006fa0003a51e1491c1bd17200007b214e000000000026a00000000000000000000c9800000000007240002959900a141300c213641845e0000000096039b2ec1cc800053c000000000000034900a40000251711ba00007bf00000000007840000ef8d028c300014041ce0a3017066800070129982d8238742456a1a03386d620596888782363121a6c0fa2b31db04945c239135f0000a1809744c9b14dec64a1f98160bf46d944b1560c960131860da41166502ed2304f925f90001bd400068f1fe175049c3640001ffc0000000000000db42c13d5924cf042e532900000004071929b3cb060000000000f5c00023200000003ef000163112e0ed1198844abe0140b118c8cba0880000000482547151866c0005b843b80008345a51ea000037646d0001c50af046e2348968a6e52a43d191c000000000000102e8800000c04bfe00012d80000000001a9000116036f0560000918000000000089c00000000800006481a319acfc8135000090cd7000035c8000fc21053c70d28f6e1b00000000efa05600000003ba1f40000a3c000000000000000084f1c680b000000028f9f28c6c00000000000000000000000b545bc31d131cdae67419500001d25382ae80007ea00000019680904c51f70b58a3c31600010d44fa0002778000e7a0bd25d800000004e22607f4eba15e23f1be00000000000f28a5e2f700005c8ad66e0000201074a4a
  | 21 => 0x8936a80005283a93ea12e03dc57c0000bf44ba0001f41eb4fec5750fd853c4703371298cd51aa00029c966c00000000010b8b8235d2d30e08eea2672c700000000001540000baa000000000093848d00000011283cd3ac0000e8862e42d089cd500000e0104c10e0001b2973c4de0000ca8330000323336000086e00024400000007e00dc13a8000518000020d18856d3d300005f60fd2bc80000001df3dd045c0005c836312f4d5456f00013c00006df0000000e1e2da37d8bcc9a28d614c141cbe6883000059ccc86ad2ad18787b081426480010da3a036a092491e0f114d087c0000003ed00011166622310000000000000000000000000000000000000000000afc8af02301b4d146bc2ab962800004c103a0709960003e61a0ce1407830e8eb8dda5860c60000b584b13c7800018000000496b4ba415f00018d487438937f1248ee236728a00004482bf20491140001d9444800020c09a2b896482a200000000010ac000000000041c175000000000014000000000006c903f80000005de03d1534c8600027183c89a81fe2c2a00000000031886a4db64b7000000000060941c9af45dc3f000000000001943a68f3c2505b2292800000000030b1a503f84a200021d47862c80ce8000bc40000450d384646c01b91b785807db4669558cac0001fd01cc0003450000bc41dc86e2a91ded07638526b15302a641b0001804e6a11324200000000a21b020a8a2a0120498b0c3bc6423ca907c00018800017d800009b000232400036a3bd000000005f07b80008240000001d68afa40202e80000003dd21c1e511a2576227a0ac0000001328ca4ac02d400000008521a441e98c0c5a7fe00010f40006123680000ce025c2b380d8aaa0630001bf0e262991529fa070604518a13407d86273be2190df4845290144ca4e00037591944c63663d79e44b1e0000810d60a1015c19884645d037828b80010246f20000000ed82a63bf9e040000003c41d1c7c6000000062c12412202521a800085b000216000000011f1e4000000000021f80002cb0000d640000000000000da400000004c4bca00031f971474658200008080004fa2290dc083267b33aa23473a000000182c0007f200000000006ab29911cc3d65102b09b38d460050000000b260cb21f879cc306491e420fcd0a6730541d90ca25721e01afc8487a8073229ccd409f000000000010b11f9b8830a6ae1ca22b91c45fc0bc0ee80000fb39402403a2000373203c9c06781d51ac91446820000b0807689e3df000044a60522a85508948bb3f8068000000000006a875085f1cc000037271500f8000424169000185000046811580000006902bf85e906000000017d00000004288000dfa000154800038a000000000064228b30a80840002bb000000014027e2330fc486400007e187c0ce47741a8e
  | 22 => 0x2093da8f38b125f206f8f70a4200000013280a00301fd97bc02e13c24c893c61a77906a1a206e83af0000008a8a00044100002520370001c180000002da00000008220000000000634000168c1002612b81a4cd000b9000075cc0c00046e0868a9227746b90a011c6e426c074cf760ec08202991be7c10758f809fc7fa3ab93c830e31038d2124a087870b802fce0432405909546f23d50f296e8a8438107507e0fd81c4047a0c41fc8a42df95cc4d8000000127416238e2061f1000053f443800000016e20821d851000041296800000721e580007643b416600c8000000334830467600003080011700f62d80000de629e14a8000cc244d0000000de000039b80007cc39e24800f400081f0000000ec000000000010a600021c8c740003c50001d7c0006970000000a2400032c0424cc660e18100000004971e1000072c79c0a5800000083c2fa8290fa087100e8bd0e547210ae800082a6dc00016100008bf00015a41ba6f9000000017c4f800000010c6865000233c0007d6231a23d1666a50f7a1348f62350e601e40005b72af1cbcf9042700003346a283319980000000000000000cca4422e4800000008913d90b057c00036c01d400080e01c83704a840a41098348e0000000000028a3ea00002a8000062000000000053000019f502200000000000000ff0721da02004082a8014c69600000007dcf78000000141435a13633e00e8ed200002118a02d459d0000d108922450001a64bcc2481e6090859a84b1568b7002a35e3208090fe8000000000000000011481a4c18000448000058812d0000000000000438083c3e63f83fca17061c53d00002845c06190000000d2250b000000000072d0cc80001603d60000bf8a38283417928c5ce11802f031c8d828912f937076081d13f90800002f240f1884d1826215d198112243018200002ec52d3d48c18a880f83f2800000073f257174c68000000000000000000001c7c0002801bd0c6c00028c0ed88b500a1462f68000adc00000013006a639712389c400034c22c800000000000000001bc4
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x401a09536004358b4100506659545c043cc401a09546004358b3100506659545c0434c40114593e11754842100449653835d521084011259420175484210045164c805d52108401c057559163484210048a6508054960084012499320152580210048c65080545600840125193201515802100498241854856008401261952012158021004a86508048560084012c193201215802100688616644856008401a2185591215802100690616634856008401a418558d21580210048a6508754960084012499321d52580210049864487549600840124993e1152580210049864784549600840122994e0d5258021004986478354960084012319421d51580210049464c8754560084012619221d51580210049464f84545600840126192e1151580210048c65383545600840126192e0d51580210049866242545600840164193909515802100498662325456008401621948c9515802100498661529056008401a418354a415802100498661528c56008401a218454a3158021004986548748560084012a19421d2158021004b064c87485600840126097615215802100498e5185485600840126393615215802100588650754856008401641931d52158021004986578448560084012c193e1121580210049866354485600840164193d5121580210049866154485600840126195e0d2158021004a865383485600840126198d4d2158021005886535348560084012619854d215802100506659435c04314001a094360043588500068450d8010d611400146196485700845000708591215c02114001c416348570084500048564782550635000120d92e055418d4000483648805506350001215912015418d4000701551725c46350001c09545c97018d4000704551715c06350001a095360043588400068454d8010d611000141a965517010e3000446a5f83551408c001a05826046454d300060661d80191534c001a09826006454d300068460580191534c001814646077254d300060319182dc5534c00101d981907054d3000603191821c1534c001814646047054d3000486a5b8454e404c00181876615435013000506659545c0430c001a09546004358830006845518010d610c00124593e11521852000489653835486148001c05745cd521852000489650805486148001245932015218520007085d1525c06148001c4173549701852000708591515c02108001c4163545700842000518a59525c0218400116297e0552482100051164f741895144001a058460c62545100050965373189514400186187600625451000688611801895144001a4183600625451000419660621c151440018258418870545100061160c621c1514400126296e095188110006181d985485204400146196549700841000708591525c02104001c41635497008410
  | 1 => 0x123095c7e0238a00fc0f03a6ce618000004a000e9d80097000c91600121a8c84b4a088c40903104a8312b278d0a81787c6ea40e240b87f48a54503b3296c7a194c80052883780000003b9c0b03e000002a6700000cc0315a0c0000161d000004229800481a274da00029288a9c470980000391b00260461ac00551d0d49c4d52800004624974f6361093d4ea0289e1040043000220000000f85e00000a00000000006e070000008439480000000013e000523d02004d000a61e2c90d4404002a42c27212345a000b800d200060001a003d13034001c2152c20000b9129849a8c6639238f114402f840fa790584cea5a22284c6141524800301186c00010800060100031b0401034c0007000f08002205100700270c03000a1b000605000037000402040c0006020001020f0001001a000009000300445647825d54310c0110d92e057550c4300443648805d54310c01115912017550c4300581655435896110c012299220154580430048c644805516010c01249922015358043004946448054d6010c01218906154358043004866548050d6010c01289922014358043004a46448050d6010c016099550e625804300582655435896010c016119550e615804300584655435856010c012199321d54580430048a648875516010c012319121d54580430048664f825516010c0123191e0954580430048664f815516010c0122992e055458043004866508754d6010c012499221d5358043004946448754d6010c0121994e095358043004946478254d6010c0121994e0553580430049264b8154d6010c012199521d4358043004a26488750d6010c012919121d43580430048625d8550d6010c0121b92615435804300486e458550d6010c01609921d54358043005846447550d6010c0121995e094358043004a46478250d6010c0121995e054358043004a264b8150d6010c014199650d7010f520068450d8010d61d48014199654d7010f420068454d8010d61d0801419965517010f32006845518010d61cc801419965517010d3200506659435c043d4401a09436004358b5100506659535c043d0
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x75806000404489005000500000000c00080004413444830aa1ac021802211a12418550d6010c01104d112ec2a86b00860088468497615435804300442343c930aa1ac021802209a2e458550d6010c01110d2120c2a42b00420089068c906152158021004443484bb0a90ac010802241a325d854856008401120d1f28c2a42b004200888693936152158021
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 70
  | 6 => 2068
  | 5 => 5422
  | 4 => 2275
  | 3 => 170
  | 2 => 12
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
  | 7 => packedAt gbK7 (1981+((h/23+packedAt gbK7 (1820+(h % 23)*7) 7) % 85)*8) 8
  | 6 => packedAt gbK6 (84784+((h/689+packedAt gbK6 (76516+(h % 689)*12) 12) % 2730)*13) 13
  | 5 => packedAt gbK5 (285554+((h/1807+packedAt gbK5 (260256+(h % 1807)*14) 14) % 11523)*14) 14
  | 4 => packedAt gbK4 (143321+((h/758+packedAt gbK4 (134225+(h % 758)*12) 12) % 3304)*13) 13
  | 3 => packedAt gbK3 (12348+((h/56+packedAt gbK3 (11900+(h % 56)*8) 8) % 225)*9) 9
  | 2 => packedAt gbK2 (992+((h/4+packedAt gbK2 (972+(h % 4)*5) 5) % 28)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fffc3060e0307ffe0fffe03fc039cf00f3cf
  | 1 => 0xfe0f83c07f003f8787f0f0ffc3ccd6b4334d33
  | 2 => 0xfff003ff80003ff807ff00fffc30e738c38e3c
  | 3 => 0x3ffffffc00007ffff00003f07c0fc0fc0
  | 4 => 0x3fffffffffff8000000003ff800fff000
  | 5 => 0xfffffc000000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x108000002000088001102000000001001045
  | 1 => 0x520d0940790294851290a24a838c5294314512
  | 2 => 0xa5a012bc80052950252a04953830a528c28a28
  | 3 => 0x308420d52a49800007ccce01889507c0540f80
  | 4 => 0xc108432a54963e6670000006112af800abe000
  | 5 => 0xf9ce780c18180c4441888818223ffffe000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffeaeaeaffeaeae8ffeaeaeaffeaeae8ffeaeaeaffeaeae8ffeaeaeaffeaeae8ffeaeaeaffeaeae8ffeaeaeaffeaeae8ffeaeaeaffeaeae8ffeaeaeaffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14530
namespace PEqualNP.Outside.L_meta_14530
open PEqualNP.Outside.L_meta_14530.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
theorem alls0 : ∀ k ≤ 2, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 1 := bs3_2_0
theorem alls3 : ∀ k ≤ 2, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
theorem alls4 : ∀ k ≤ 2, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 1 := bs5_2_0
theorem alls5 : ∀ k ≤ 2, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 12 := bgb_2_0
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
theorem bgb_3_160 : Interval gbAtlas 3 160 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 170 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat bgb_3_96 (concat bgb_3_128 bgb_3_160)))
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
theorem bgb_4_2272 : Interval gbAtlas 4 2272 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2275 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))))) (concat (concat (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672)) (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)))) (concat (concat (concat bgb_4_864 bgb_4_896) (concat bgb_4_928 bgb_4_960)) (concat (concat bgb_4_992 bgb_4_1024) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))))) (concat (concat (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824)) (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)))) (concat (concat (concat bgb_4_2016 bgb_4_2048) (concat bgb_4_2080 bgb_4_2112)) (concat (concat bgb_4_2144 bgb_4_2176) (concat bgb_4_2208 (concat bgb_4_2240 bgb_4_2272)))))))
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
theorem bgb_5_5408 : Interval gbAtlas 5 5408 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5422 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)))) (concat (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))))))) (concat (concat (concat (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)))) (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360))))) (concat (concat (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 (concat bgb_5_3488 bgb_5_3520))) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680)))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840))) (concat (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936)) (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)))))) (concat (concat (concat (concat (concat bgb_5_4064 bgb_5_4096) (concat bgb_5_4128 (concat bgb_5_4160 bgb_5_4192))) (concat (concat bgb_5_4224 bgb_5_4256) (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)))) (concat (concat (concat bgb_5_4384 bgb_5_4416) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512))) (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))))) (concat (concat (concat (concat bgb_5_4736 bgb_5_4768) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 bgb_5_5120) (concat bgb_5_5152 (concat bgb_5_5184 bgb_5_5216))) (concat (concat bgb_5_5248 (concat bgb_5_5280 bgb_5_5312)) (concat bgb_5_5344 (concat bgb_5_5376 bgb_5_5408))))))))
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
theorem bgb_6_2048 : Interval gbAtlas 6 2048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2068 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 70 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 3 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 3 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 3 := by
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
def fullRoots : List Sig := [inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffefefefffefefcfffefefefffefefcfffefefefffefefcffeaeaeaffeaeae8fffefefefffefefcfffefefefffefefcfffefefefffefefcffeaeaeaffeaeae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14530.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[8,4]⟩,⟨.and,[9,7]⟩,⟨.and,[5,6]⟩,⟨.or,[1,2]⟩,⟨.or,[12,7]⟩,⟨.or,[5,6]⟩,⟨.and,[13,14]⟩,⟨.and,[0,4]⟩,⟨.or,[10,11]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14530

open PEqualNP.Outside.L_meta_14530 in
theorem PEqualNP.Outside.L_meta_14530 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
