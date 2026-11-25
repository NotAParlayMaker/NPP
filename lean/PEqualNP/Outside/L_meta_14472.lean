import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14472.Model
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


end PEqualNP.Outside.L_meta_14472.Model

namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
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

end PEqualNP.Outside.L_meta_14472

namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff07c1ffff8783c3c0fffc3c0fffe8cf33f
  | 2 => 0xfffff801fffff803fc00ffffc00ffff30fc3f
  | 3 => 0xf03ffffe0fc1fffc0000f83ffff1f01c0cfcc
  | 4 => 0xf003ffffff001ffffffff003ffffe001ff0ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x912913212a29083a1424a2a5424a29548c5315
  | 2 => 0x2252241a545213842a41454aa41452a930ac2a
  | 3 => 0xc49b494b06833cce422209e0eaa61c0dc0c54c
  | 4 => 0x608210001841108c88600311188030150ab0
  | 5 => 0x88830c6398e39e6733338e70222018c1eaf000
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xffffc0c0ffc0c0c0ffffc0c0ffc0c0c0ffffc0c0ffc0c0c0ffffc0c0ffc0c0c0ffffc0c0ffc0c0c0ffffc0c0ffc0c0c0ffffc0c0ffc0c0c0ffffc0c0ffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
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
  | 0 => 0x3c3fffc7c3ffffe1870e0fffc387ffff09f0ff
  | 2 => 0xc03c7ff803c7c3fe07f00f0ffc071e1fb13c93
  | 3 => 0x3f87fffc07fc3ff8000ff0fff81fe0c1cf1c
  | 4 => 0xffc007fffff8003ffffff000ffffe000fe0fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x440042050100008202421100818288085025
  | 2 => 0x9a8b3491aa8aa62e4590a58ae4325456b12c92
  | 3 => 0xa3115524a0942273488109a869501942c18518
  | 4 => 0x8002201000088841124200092244004120ac0
  | 5 => 0x3222443633273339e6c9cecc20409198edf000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xffffaaa0ffaaaaa0ffffaaa0ffaaaaa0ffffaaa0ffaaaaa0ffffaaa0ffaaaaa0ffffaaa0ffaaaaa0ffffaaa0ffaaaaa0ffffaaa0ffaaaaa0ffffaaa0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
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
  | 0 => 0x3c3fffc7c3ffffe1870e0fffc387ffff09f0ff
  | 1 => 0xc03c7ff803c7c3fe07f00f0ffc071e1fb13c93
  | 3 => 0x3f87fffc07fc3ff8000ff0fff81fe0c1cf1c
  | 4 => 0xffc007fffff8003ffffff000ffffe000fe0fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x440042050100008202421100818288085025
  | 1 => 0x9a8b3491aa8aa62e4590a58ae4325456b12c92
  | 3 => 0xa3115524a0942273488109a869501942c18518
  | 4 => 0x8002201000088841124200092244004120ac0
  | 5 => 0x3222443633273339e6c9cecc20409198edf000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffffaa88ffaaaa88ffffaa88ffaaaa88ffffaa88ffaaaa88ffffaa88ffaaaa88ffffaa88ffaaaa88ffffaa88ffaaaa88ffffaa88ffaaaa88ffffaa88ffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
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
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 2 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
def s4K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*4) 4
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (5+((h/1+packedAt s4K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 3 => 0x78ffe00fffc00fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 3 => 0x7851aae4986af80
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 15 s4Pos s4Neg, 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
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
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x11158a0e0f88810709819d1695078b091d998a971884821a8000131c8000938012841b0e9b829e1f03059a051e9f800c1c03900011800020962019080d148f1214060b8d8010868000000c800000179804000a182830400401022c40602840090e18081007fd5001fe54005f95001fd54007f150017c54007fd4c017f53007f94c01fd53005f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x44000fec8220005feca90002fe65480017eb2a4000bf19520005fec890002fe64480017eb224000bf19120006fca8900037c54480017fb1a4000bf98d20005fac690002fc6348001bfa9a4000df54d20007dc8490003ed4248001f71924000fb4c920005fec290003f761480017bb0a4000bf18520007e8c290002f46148001f790a4000fb48520006fea0900037d5048001fd9024000fb88120005feca10002fe6508001bf32840009f99420005faca100037d65080013eb284000bf19420005fec810002fe6408001df3204000af99020005fac810003bd64080015eb204000bf19020006fca8100037c54080017fb184000bf98c20007bcc610002de63080017eb184000f758c20005bac610002fc6308001bfa984000df54c20005fcc410002fe6108001fb3084000bd98420005fac210003f561080017ab084000fb88420007d84210002fe6008001bfa804000df54020007de4010003fa2008001f69004000fe48020005fecb88002fe65c40017eb2e2000bf19710005fec988002fe64c40017eb262000bf19310006fca9880037c54c40017fb1e2000bf98f10005fac788002fc63c4001bfa9e2000df54f10005fec588002fe62c40017eb162000bf18b10007ec8388003f541c4001fb18e2000fd4c710007ec4388003f521c4001bfa862000df54310005fecb08002fe6584001bf32c20009f99610005facb080037d65840013eb2c2000bf19610005fec908002fe64840017eb242000bf19210006fca9080037c54840017fb1c2000bf98e10005fac708002fc6384001bfa9c2000df54e10005fec508002fe62840017eb142000bf18a10005fac308003f72184001fa10c2000bf98210006fea1080037d5084001fd1042000fe48210007ee2108003fb10840017fb2a2000bf99510005faca88002fc65440017fb222000bf99110005fac888002fc6444001bf2a22000df15110005fec688002fe63440017eb1a2000bf18d10006fea6880037d53440017fb122000fbd8910005dec488002fe62440017eb122000bf18910007d8c488002ec6244001fb20a2000fd50510007ec6288003f53144001fb10a2000fd48510006fea0880037d5044001fd1022000fe48110007f62088003f610440017fb282000bf99410006fcca080027e65040017eb282000df59410004faca08002fc65040017fb202000bf990100077cc808002be64040017eb202000ef590100057ac808002fc6404001bf2a02000df15010005fec608002fe6304001ef3182000b798c10005fac608003dd63040016eb182000bf18c10006fea6080037d53040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc62040017f3082000fdc8410007e84208002fe6004001bfa802000df54010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x77e5410003be2a08000bf98c40007bcc620002de63100017eb188000f758c40005bac6200037f5310001bea988000bf98840007dcc420002ee62100017eb108000fb58840005dac420002fe6110001fb3088000bd98440005fac220003f561100017ab088000bf98040006fea0200037d5010001dfa008000fe900400077a8020003f940100017fb2e6000bf99730006fccb980027e65cc0017eb2e6000df59730004facb98002fc65cc0017fb266000bf99330005fac998002fc64cc001bf2a66000df15330006fea7980037d53cc001ef21e6000f750f30005fcc598002fd62cc001ef9966000f74cb30005fcc398002fd61cc001ef98e6000f74c730006fea1980037d50cc0017fb2c6000bf99630006fccb180027e658c0017eb2c6000df59630004facb18002fc658c0017fb246000bf99230005fac918002fc648c001bf2a46000df15230005fac7180037f538c001ef29c6000df54e30007baa7180035d538c001efa1c6000f710e30005fcc518002fd628c0017f30c6000bf58630005fcc1180037f508c001bea846000fe90230007f28118003df308c001fd9846000bfd9530005fcca980037e654c0013f32a6000bf59530006faca980027d654c0017e32a6000bfd9130005fcc898002fd644c0017e3226000df95130006f8a8980037f534c001bea9a6000f790d30007ba8698002ff624c0017e3126000f7cc930007ba6498002ff614c0017e30a6000f7cc530007ba62980037f504c001bea826000fe90130007f28098003fb304c001ef1826000bfd9430005fcca180037e650c0013f3286000bf59430006faca180027d650c0017e3286000bfd9030005fcc818003be640c0015f3206000bf590300077ac818002bd640c0017e3206000df95030006f8a818002fe630c001bfa986000f794c30006faa618003dd530c001aea986000f7d0c30007b88618002fe620c001f73106000bb98830005fac418003ed620c00176b106000bf98430007ecc218002f6610c0017eb086000fd58430005eac218002fe600c001bfa806000df54030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c80017eb2e4000bf19720005fec990002fe64c80017eb264000bf19320006fca9900037c54c80017fb1e4000bf98f20005fac790002fc63c8001bfa9e4000df54f20007dc8590003ed42c8001f71964000fb4cb20005fcc390002fd61c8001f790e4000fb48720006fea1900037d50c80017fb2c4000bf99620006fccb100027e65880017eb2c4000df59620004facb10002fc65880017fb244000bf99220005fac910002fc6488001bf2a44000df15220005fec710002fe63880017eb1c4000bf18e20006fea7100037d53880017eb144000bf98620005fac310003ee2188001f610c4000bf98220006fea1100037d5088001f79
  | 2 => 0x50006fa65a80037c32d4001bfb0ea000df98750006fac3a80037c61d4001bfa0ea000df90750006fa83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f59650005fcc928002fd6494001bf2a4a000df15250005fcc728002fd6394001bfa9ca000df54e50005fcc528002fd62940017f30ca000bf58650005fcc1280037f5094001fda84a000bfd9150005f8c8a80037f5454001bf2a2a000df55150006f8a8a8002ff63540017e31aa000dfd4d50006fca6a80037d5354001be29aa000bfd8950005f8c4a80037f5254001bf292a000df54950006f8a4a8002ff61540017e30aa000dfd4550006fca2a80037d5154001be28aa000fed4150006fca0a80037f6454001bf322a000df59150006f8c8a80027c6454001bfb1aa0009fd8d50006fcc6a80037d6354001be31aa000dfd0d50006fc86a80037d4354001be21aa000dfd8950006fcc4a80037d6254001be312a000dfd0950006fc84a80037d4254001be212a000dfcc950006fc64a80037d3254001be192a000dfd8550006fcc2a80037d6154001be30aa000dfd0550006fc82a80037d4154001be20aa000dfcc550006fc62a80037d3154001be18aa000dfc8550006fc42a80037d2154001be10aa000dfd8150006f6c0a8002fe65140013f328a000bf99050005fac8280037e5414001be2a0a000bf98c50005fac6280037f5314001bea98a000bf98850005fac428002fe61140017eb08a000bf98050006fea028003fa5014001bea80a000fe54050005fecba00077f65d00013fb2e8000bf99740005facba0002fc65d0003be32e80009f1974000efca9a00077c54d00017f31e8000bf58f40006fea7a00037d53d0001dfa1e8000ef50f40005fcc5a0002fd62d0001dfa168000ef50b40005fcc3a0002fd61d0001dfa0e8000ef50740006fea1a00037d50d00017fb2c8000bf99640006fccb200027e65900017eb2c8000df59640004facb20002fc65900017eb248000df95240006f8a920002fe63900017eb1c8000dfd4e40006faa720002fe62900017eb148000bf98640005fac320002fe6090001bfa848000fe94240006faa120003f95090001bca848000efd0240007f68120002ff6550001bfb2a80009fd9540005fccaa0002fd65500017e32a8000df19540004f8caa00037e5450001be2a28000bfd8d40007bec6a0002df63500017e31a8000f718d40005b8c6a00037f5350001bea9a8000efd0d400077a86a0002ff62500017e3128000efd09400077a84a0002ff61500017e30a8000efd05400077a82a00037f5050001fd2828000df54140007f2a0a0003795050001fda028000ef90140005feca20002fe6510001bf32880009f99440005faca200037d65100013eb288000bf19440005fcc82000
  | 3 => 0xe32a6200bfd9131005fcc898802fd644c4017e3226200df95131006f8a8988037f534c401ef29a6200df54d31007baa6988035d534c401efa1a6200f710d31005fec498802fc624c401ef9926200f74c931007ec8298803f5414c401fb98a6200f78c531005fec098802fc604c4017fb286200bf99431006fcca188027e650c4017eb286200df59431004faca18802fc650c4017fb206200bf99031005fac818802fc640c401bf2a06200df15031005fcc6188037f530c401bea986200bf98831005fac418802fe610c401ef9886200fd8c431007ba6218803f5310c4017f3006200bf58031005fecb90802fe65c84017eb2e4200bf19721005fec990802fe64c84017eb264200bf19321006fca9908037c54c84017fb1e4200bf98f21005fac790802fc63c8401bfa9e4200df54f21007ec8390803f541c8401fb18e4200fd4c721005fcc190802fd60c84017fb2c4200bf99621005facb10802fc65884017fb244200bf99221005fac910802fc6488401bf2a44200df15221005fec710802fe63884017eb1c4200bf18e21006fea7108037d53884017eb144200fb90a21007da8510803ee3288401f69944200bf98621007de4310803f721884017f3044200bf58221005feca90802fe65484017eb2a4200bf19521005fec890802fe64484017eb224200bf19121006fca8908037c54484017fb1a4200bf98d21005fac690802fc6348401bfa9a4200df54d21007ee4290803ee21484017fb024200bf18121005feca10802fe6508401bf32842009f99421005faca108037d65084013eb284200bf19421005fec810802fe6408401df3204200af99021005fac810803bd64084015eb204200bf19021006fca8108037c54084017fb184200bf98c21007bcc610802de63084017eb184200f758c21005bac610802fc6308401bfa984200df54c21005fcc410803ee4208401f6a104200fb8c821007da6410802fe6108401fb2084200fd50421007ec6210803f53108401f79084200fd88421007da4210803f52108401f29084200bf98021007f4c010802fa60084017eb004200fe58021005f2c010802fe64d40017eb26a000dfd5350006fca9a80037d54d4001be2a6a000bf98f50007bcc7a8002de63d40017eb1ea000f758f50005bac7a80037f53d4001bf29ea000df54f50006f8a7a8002fe62d40017eb16a000dfd4b50006fca5a80037d52d4001be296a000bf98750005fac3a80037f51d4001bf28ea000df54750006f8a3a80037f64d4001bf326a0009f99350006fac9a80037c64d4001bfb1ea000df98f50006bcc7a80037d63d40013eb1ea000d758f50004bac7a80037c63d4001bfa1ea000df90f50006fa87a80037c43d4001bfb16a000df98b50006fac5a80037c62d4001bfa16a000df90b50006fa85a80037c42d4001bf996a000df8cb
  | 4 => 0x3ed320c8017f3086400bf58432005fcc019002fd600c8017f326a200bf59351006fca9a88037c54d44017f31ea200bf58f51006fea7a88037d53d44017f316a200bf58b51006fea5a88037d52d44017f306a200bf58351005facb28802fe64944017eb24a200df95251006f8a928802fe63944017eb1ca200dfd4e51006faa728802fe62944017eb14a200bf98651006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bf2a2a200df15151005fec6a8802fc6354401bfa9aa200df54d51005fec4a8802fc6254401bfa92a200df54951007eea2a88037e51544017fb02a200bf18151005fcca28802fe64144017eb20a200df95051006f8a828802fe6314401ef318a200b798c51005fac628803dd63144016eb18a200dfd4c51006faa628802fe62144017eb10a200bf98451006fea228803f65114401bea88a200fd54451005fcc028802fd60144017fb2e8200bf99741005facba0802fc65d0403bf2a68201df15341005fcc7a0802fd63d0401bfa9e8200df54f41005fcc5a0803ee62d0401773168200bf58b41007dac5a0802ed62d0401dfa168200ef50b41005fcc1a0802fd60d04017fb2c8200bf99641006fccb208027e65904017eb2c8200df59641004facb20802fc65904017eb248200df95241006f8a920802fe6390401ef31c8200b798e41005fac720803dd63904016eb1c8200dfd4e41006faa720802fe62904017eb148200bf98641007eca320803f55190401dfa0c8200fdd0641005fcc120802fd60904017fb2a8200dfd9541004fecaa0802fe65504017eb2a8200bf19541006f8caa08027c6550401bf2a28200df15141005fec6a0802fc6350401bfa9a8200df54d41005fec4a0802fc6250401dfa128200ef50941007eca2a0803f55150401fba0a8200ef90541005fec0a0802fc60504017fb288200bf99441005faca20802fc65104017f3208201df9504100ef8a820802fe63104017eb188200dfd4c41006faa620802fe62104017eb108200bf984410077e8220803f64110401dea088200fd50441005fcc020802fd60104017fb2e6200bf99731006fccb988027e65cc4017eb2e6200df59731004facb98802fc65cc4017fb266200bf99331005fac998802fc64cc401bf2a66200df15331006fea798803de53cc401bea9e6200f754f31006baa798803df43cc401ee21e6200bf98b31007dcc598802ee62cc4017eb166200fb58b31005dac598803df32cc401ee9966200bf98331005fac198802ff658c4017f32c6200bf59631005f8cb18802ff648c4017f3246200bf59231005f8c9188037e548c401be2a46200bf58e31006fea7188037d538c4017f3146200bf58a31005fcc318803f6418c401faa0c6200f7cc631007ee6318802fe608c4017eb046200bfd9531005fcca98802fd654c4017
  | 5 => 0x8252005fec8a9002fc6454801bf2a2a400df15152005fec6a9002fc6354801bfa9aa400df54d52007dea4a90037e52548017fb0aa400bf18552005fec0a9002fc60548017f328a400bf99052005fac8290037e5414801be2a0a400bf98c52007bcc629002de63148017eb18a400f758c52005bac6290037f5314801bea98a400bf98852006fea429003ee5214801bea90a400fb54852005fcc229002fd61148017f300a400bf58052005fecba1002fe65d08017eb2e8400bf1974200efca9a10077c54d08017f31e8400bf58f42006fea7a10037d53d08017f30e8400fd98742005ecc3a1002fd61d0801fab0e8400bd58742005fcc1a1002fd60d08017fb2c8400bf99642006fccb210027e65908017eb2c8400df59642004facb21002fc65908017eb248400df95242006f8a921002fe6390801ef31c8400b798e42005fac721003dd63908016eb1c8400dfd4e42006faa721002fe6290801f72948400fb54a420077e8521003ef42908017f30c8400bf58642005fcc121002fd60908017fb2a8400dfd9542004fecaa1002fe65508017eb2a8400bf19542006f8caa10027c6550801bf2a28400df15142005fec6a1002fc6350801bfa9a8400df54d42007dca4a1003ed5250801f7a128400ef90942005fec2a1002fc61508017fb028400bf18142005feca21002fe65108017eb288400bf19442005fcc8210077e5410803be2a08400bf98c42005fac6210037f5310801bea988400bf988420077e8421003ee4210801dea108400fb50842005fcc221002fd61108017f3008400bf58042005fecb99002fe65cc801bf32e64009f99732005facb990037d65cc8013eb2e6400bf19732005fec999002fe64cc8017eb266400bf19332006fca9990037c54cc801bfa9e6400f794f32006faa799003dd53cc801aea9e6400f7d0f32007b88799002fe61cc801fb30e6400bd98732005fac399003f561cc8017ab0e6400bf98332005fac199002ff658c8017f32c6400bf59632005f8cb19002ff648c8017f3246400bf59232005f8c9190037e548c801be2a46400bf58e32006fea7190037d538c8017f3146400fb90a32007da8519003df328c801f79946400bf98632005fac319002fe608c8017eb046400bfd9532005fcca99002fd654c8017e32a6400bfd9132005fcc899002fd644c8017e3226400df95132006f8a8990037f534c801ef29a6400df54d32007baa6990035d534c801efa1a6400f710d32007dc8499003ed424c801f79926400f78c932005fec299002fc614c8017fb026400bf18132005feca19002fe650c801bf32864009f99432005faca190037d650c8013eb286400bf19432005fec819002fe640c8017eb206400bf19032006fca8190037c540c8017f3186400dfd4c32006faa619002fe620c801ef9906400fb8c832007ba6419
  | 6 => 0x1be2a6a600bf98b53005fac5a9802fe61d4c017eb0ea600bf98353005fac1a98037f64d4c01bf326a6009f99353006fac9a98037c64d4c01bfb16a600df98b53006fac5a98037c62d4c01bfb0ea600df98753006fac3a98037c61d4c01bfb06a600df98353006fac1a98027d60d4c01be306a600bf59653004facb29802fe6494c017eb24a600df95253006f8a929802fe6394c01bfa9ca600f7d4e53005fcc529802fd6294c017f30ca600bf58653005fcc129802fd6094c017fb22a600bf19153006fea8a98037e5454c01beaa2a600df15153007bea6a98037e5354c017fb12a600bf18953005fec2a9802fc6154c017fb02a600bf18153006fec8a98037e6454c01beb22a600df19153004f8c8a98037f6354c01afb1aa600dfd8953006fcc4a98037d6254c01be312a600dfd8553006fcc2a98037d6154c01be30aa600dfd8153004fec0a98037e6054c01beb02a600df18153005fcca298027e6514c017f320a600bf59053006fca8298037c5414c017f318a600dfd4c53007bca6298037d5314c01eea98a600bf98853005fac429802fe6114c017eb08a600bf98053005fac029802ff65d0c03bfb2e86009fd9743005fccba1802fd65d0c017e32e8601df19743004f8cba18077e54d0c03be2a68600dfd4f43006faa7a1802fe62d0c017eb168600bf98743005fac3a1802fe60d0c017eb068600bfd9643005fccb218037e6590c013f32c8600bf59643006facb218027d6590c017e32c8600bf59243006fca9218037c5490c017f31c8600dfd4e43007bca7218037d5390c01eea9c8600d754e430077e8721803df4390c017f3148600bf58a43005fcc321802fd6190c017f3048600bf58243005fecaa18037f6550c013fb2a8600bf99543005facaa1802fc6550c01be32a86009f19543006fca8a18037c5450c01bfa9a8600f794d43006faa6a1803dd5350c01aea9a8600f7d0d430077c86a1802ff6250c017e3128600bfd8543005f8c2a1802ff6050c017e3028600bfd9443005fcca218037e6510c013f3288600bf59443006faca218027d6510c017e3288600bf9904300efca8218077c5410c017f3188600dfd4c43006faa621803bf4310c01ef2188600ef50c43007ba86218039d4310c017f3108600fb98843005dcc421802fd6210c01f6b108600bb58843005fcc221803f66110c017b3088600bf58443007eac221802f56110c017f3008600fe98043005f4c021802fd6010c01fcb008600be58043005fcc9a9002fd64d4801bf2a6a400df15352005fcc7a9002fd63d4801bfa9ea400df54f52005fcc3a9002fd61d48017f306a400bf58352005facb29002fe64948017eb24a400df95252006f8a929002fe63948017eb1ca400dfd4e52006faa729002fe6294801bfa94a400fbd4a52005fcc329002fd61948017f304a400bf5
  | 7 => 0x2803008000c00400400400802004800000000000001400000400001807c0280040040700000080040340d800000402c00801407000400400000000000c00000c00000006800000001c00401401005000801c04405c0000000101440000dc01001000000000000006000800401000c01800000c00000c00c00c02400401402000800400c01c04c01800001001000000c00000400800005001000001400001002801800007801401005001000000000011000c06400000000802801c01001405404800003001000c00001404000800407802c00000809001c00c00000000000000000000c03000000c00400c00c00004401400400004001400800c03400000000000400c01400800402000000001c00801401400401400001800000000400401000000c11000c01c00000800004801800803c01400400000000403800c00c00005801000802000800404000c02c00808400800001400000000000000001c00405c00000000002401000402400c02c0640d00100080040240140d003800000000000002401c00002002000806c00000000001c00000800801001c00800807400004800c00003c03c00800000400002800800006c06807c00400406c00002000000800000c00c004024014018004028000000000000000010000004000000004058014008000010010017f31ea800bf58f54005fcc5aa002fd62d50017f30ea800bf58754005fcc1aa002fd60d50017eb2ca800bf99254006fea92a003bf54950019faa4a800bf98e54005fac72a002fe62950017eb14a800bf98654005fac32a002fe60950017eb04a8009f9925400efec72a0037e6395001beb1ca8009f58e5400ef8c72a0077f6295001bf314a800df58a5400ef8c52a0077f6195001bf30ca800df5865400ef8c32a0077f6095001bf304a800df58254004fac12a0077c6095001dfaa2a800df95154005fec6aa002fc63550017fb12a800bf18954005fec2aa002fc61550017fb02a800bf18154005fcca2a002fe6415001bfaa0a800ef95054006faa82a003bd54150017f318a800f798c54005bcc62a002fd6315001eeb18a800b758c54005fcc42a003ee621500177310a800bf58854007dac42a002ed62150017f308a800fd98454005ecc22a002fd6115001fab08a800bd58454005fcc02a003fa60150017d300a800bf58054007f2c02a002f96015003bf320a8009f990540067cc82a0077f6315001bf318a800d798c54006fac62a0027d6315001aeb18a8009758c5400ef8c62a0077f6215001bf310a800db98854006fac42a0036d6215003be310a801dfd8454006fcc22a003766115001beb08a800dd5845400ef8c22a0077f6015001bf300a800de98054006fac02a0027d6015001bcb00a8009e5805400ef8c02a002fe64d4c017eb26a600dfd5353006fca9a98037d54d4c0
  | 8 => 0x9e01062bd2fb9d78da28329009c2ad0981e222025cb1e82399500f8bb2fea7433b1a60ae93c03320a05612a96133785f8270dc8e4b0a2eb2f6870a762549882029510b890c2891b5ab70000001b700000000019900000000000007e0000000940680630000a22d912294c9f8a9a2fb00000019f21680000018d9fd98b8a817f85f0e78003218e527500000000000025400e13614523b9c3ab680020599b9169268552a18400001369be1c98d608280030481e8001841c312209b25b87aa63000269800245b1b000289ac10000e28048210000e40628000c922186414a917a38162a0116511a95d94228809e0002ba80000000015628295c32682d800048a3914300007680000005ba938f98000001e2ae805a1a980033800010d0001faa4d189236ac9800230b0895b93280020c182aeeb2b9380638d224a1d58e606a9bc2eb9e30c78a185caa4b1188e3250001d300025911880000000000024c8b100000012ba8f00013727b8001d88000002f2b0f00003d80000025e8f50000daa258001c40002fd0000001022d680008a95d0661a68000000001e681c8000001be8ac00014827324d8000b79542b9ae925797989f80009b8002b1b3f14f87296f80009100017b84b8002ca8b923d81f25199e30f97528d0f8ae1ae20000000d68000000001320eaab83151468001138260002c79ca10a91d95f9cc22ca338000710002ec2ab0f08ac85eaf98000000000000428002838fc80000000000000031f33a1bf8000002ac8001748c694f07b8000000001758338dd0000960e900011c0000530000783128002f08e393480032a08100007ea920e0a9b8002aa80004e9720281ee80000033ca4380021c33687711330515280003722e9c8af900000013b00027e28a16400032f84320300000028518c14b2c403b80000023c2ac0002c880013988400025d8512ca001000002000001002800401401000000006400c00c00c00c07c00000800401000809800c01400400401400007c00002800001400801002c0100240000280200600040000b001002000001c00c00000401c00000c00800401400800c01c00405000c00000404803800000400800c05003403800000401403400801400000001401001401004c04800004c00002800401400403c01c00801800803802402004000003401c00400000000401002800001800400001400002800c00000800000401000000000000404802401400803c00c00001003000800800401404400000400400800404400001004c00400000800c00800800000001400c00802803800000400000c02c00400007805801400811408c01400c1480000240040cc00c00000000c00000803802402c0080bc01002001c01402800c02800401400000800401c02400800c00800806c00000400c0240080300280240100500700140
  | 9 => 0x5a9c6b1f9c025725895c95e2e01d822e13319b08890ba5f0ad9ec86f0e71700ba07f12a227a0795b095a1833c052316acf2918471f523f8669e1aefaa8a721319fa0b3a352581f80f4ae5249016b090ab9901120142b216aa002d5a5698a858b06251199a039e50b60000222bf9a72529bb01d1cf06ba7809e9d7130012b2e9deaddb2232d1659f30f11da8b721f8f80eb21424100d2f8008193829986aa01ae85680020e1e78001a40002e10001b822f26200016b9b93238000000119202bc14e8f000021d80b20185d00000011498701805da26805a5b0dc0100ef8000171960000000d1ad882bafe138b070001c1000188a2227488fa1780029c28c9410002cb0001b48312471728859899a53213262b01668e896d924000295000000000052ab08e30001ee0001000732d1ace2d08019fe80002b0000000001290d11d2197a8db3d0ee29132d8000fb21100014b8000001ef04b28aa64247a6a04a8008fe82e16a00018e002aa9aa20329d4ac80e9aff12b0002300000000002dc29b1b119d0c29fc8001858000001910002c2059a90a4aa2331b98b294aea1211afb3e8c8a5c06e0000001bf00ba051f20a704a00216627b27a2a907920f8a02f217d8002e608b000000000000125a2a0318ec0002170000051ce065277000000060a330a78001a91cfaed950aba30b8be0be86c0922cd9e8adc9bd8bc0001b89252de0000001391311538ebaf103231caf8ad7097aaa18d19f9d11fba5a0000002d62e70e11ca8a38bab3328124ea3493f8c5903800327000000202000086314a1ca930000002f4207219ae2b2a83023f0d88bf2faa6189380000000000000024e0b50002b8800000310b161069aa82cac48f72a10378032160ae2d400027929f0b6a4889480000013e9810002be00000009ca559f402f32b286000000267800270970929a7ea0b33200000022c0362e396ca3a2e30258000ab24f05011519c00903410ca40a1e0000991909e0ab58000411c28000000c09b698fa4600000000000020d00001500000000c00007034005380382c2c097c17a2560e588900026d8000000002280352cb8a5000089af19dc0760fd1ad3399980000cd00023e107adb29d03f00707c00003a8001050000000f29930db0000002b52670b48000001e92d3319b0cb2786c80000027a9d18f20002a40002c71551a128b9a597a9ac0f628e8819ad9ab97621005e1030198518871140eda250cc14a00006d24410a00028e0001e3928a6a91199d97e1f4b3103a2af0a90000df80026b3200000c60000ed149813a8f8580a09e70e680007780000f0000f683831d8002c28000000000aa800019000000000000305afc8001878000000000000000000000000000002128cea2f94d0c21d517e981880854318af30f78c30f5b3e2bea0601100a8f38a48cc82ea65
  | 10 => 0xa8b031ba8001f59f9a37a1e83b1b302787d0000fc2a2980800092aae210a8b2648b980416813380012180033fada0919d601a2868002239d38000000000fd80000004194380013c9d01d90000002e6a92a6030da1526ca970c1883adf0000000000002360000000af8188000001bb861aad80003d333a612eab19044a121a308013a2ee2bd869849ab39e407426e11fae997c9191ccaef337147aa80c11a481c1c61cdacc273b07adba322879c92098d82f520bb03ad4a551b616005b25e29a904a4ba81b2904e2a78ca0bd878a538201401502de9c21c4adaab7a260b31cb86121a0c430e0d091716d0e18308ef1262c18d92450999a880011d17d00000021300022d0000000003183350000a12c6135000159108a4012e0e23130b2ae59fb03688204f02f8e00de26b90f22aa50295992228800028942a6d1f383e8621fd000141b0ea7004fb2e32c2399d68ad22b0001eb2271c723b29e0000573138290001dda8885097780999ea31a1f0000000001b98000000b410900030d15aa8491ea210002f490f9d417884606d8000000000001b184200000600000000017695880018200009a8001bd1690001e132800027c8f92a3b1e0000001520000c730804796b0001862c59d292f9e607513d80d8d018ea7990e8688002719b0b34000022897000075b1a8a981e23d00000029696220409a262af59a0800000000179000034a0881f9f6127a981698001dd00018333280022280000000007b03983f9c597b0001ea80000000000032300000030a9341f696e08d80014d8002ff9448000002a70b80000a6006afa02a2650002418001d080000000015f0000440002df8000002bf0000dea66a85ab908d000173153213b24b3d8003318000000000000000000001800000002d124812300000011a2f7a77aafaf3ac69cd1df80008e80020d8001648cf0000f18b59b7a820000bb930890ad9a75a328000000481009c521bb2f0002e7a5d24205908caf628c1080468cb9b41ffad50002bc93f0001128000d4196940b3880025200033a937865a4b21d1fc148ad7a7d23700000000000020804c80008522da0a83e3099b28d28000bc80000013bac92468121b508c1ed1a3826a342e0a06a9915a0879672d81928001e480023c80025981da97810afd9bc91e1f7ab280027f840acc8000d710e03c8d50000b092c0000002cf80004d82521a8002690000001de19580000012f3040930d398502186488a2b101b8db854909a431460001578001f7163a729781f280c968879a682809158158c819a301b0c2d20001059718f40fa0831849efac0242800154a788ec8002a08000001711a000009d2bb00000020486f8a40000ea0001a23298000000003010001ec11b800000060007817a9e8000003159e80aa19c838af00002d29f08001f10cb0c4a3eb1a0
  | 11 => 0x55a090b200000012c89880e8240748000000000002ab9ab00012800000008f01a82a92db3489daae944000215800340800224afc00000027f000158000000000000249800000000294000067920ac50fb800238a2933b8001571f1a7c1471838000af000104320919a192c31b00e81618232ce901a9fa311160002689da20f19aa7d96eaa68002298000900cfb17049198a0e9559e5b288002a5b3915e80008b91c8002208001ce800000000101000000000000000260add00000000024c084b2280006a0001a78000c98bf8000000690c00a32a607c8001df0b18670002bbaf700009f300b0698cab307a0000df00000026380004c1fe0000000000950000001ebb24156a530000880130cdb02800096a6f11f2188faae43001d984590dad38ee8d99a81919112b4102a7686e9249ba0a2b11200aec93e13a8bd1aa18a00007fb3630b0002243300ff9109c080022ba14a4f8002e8a8718f0a680008686b1f9151b0211000001631c3140a583c298b2580032ca5a8d48000002508fe335a6eb101e994e2448000452661608000b029d9c79598c52840ce12d0d301b00017700a29c9db1458000002801cb2e49271a29a19db96c16f071ab61dcaa30010209ea2710d5aed13d26fb1d0f305c1c1a1b1ed8d79359739070002b48000001238439180002a512e9949ff1f019402d0001ac9ae07da99a5f91b04d0dd80026c10b1c8317800057ad000020c97f07397400000002480014c23a997000008b121b3835a119af0148c3a96000000167b309631b20390ff0caa35acd1492c387200
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe72d9410004ed72d94100047d769941000c7e74994100047d739941000c7c74594100047f73594100047f70594100047d70594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed72194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d9010004bd76990100063e65990100063d659901000e3f759901000e3c75990100047f75590100047c75590100063e65590100063d65590100063f75590100063c75590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f6711901000c7f76950100047d769501000e3e64950100063d649501000c7f76150100047d761501000e3e64150100063d64150100055d73150100057970150100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c100047e7598c100047d7598c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100065e7598c100065d7598c100065e5498c100065c5498c100065e6558c100065d6558c100069e6458c100069d6458c100065e7558c100065d7558c100065e5458c100065c5458c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c100047f76d4c100047d76d4c100063e64d4c100063d64d4c100065e63d4c100065d63d4c100047f7654c100047d7654c100063e6454c100063d6454c100065e6354c100065d6354c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e54988100066c54988100066f53988100066d53988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066e54588100066c54588100066f53588100066d5358810006e471588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa7018810004f576c8410006b564c8410006d563c8410006e562c8410004f57608410006b56408410006d56308410006e56208410005f170084100047e75980100047d75980100047d76d40100063e64d40100063d64d40100055d73d40100065e63d40100065d63d40100066e62d40100066d62d40100047f76540100063e64540100063d64540100065e63540100065d63540100066e62540100066d6254010006b564c4010006d563c4010006e562c4010004f97684010006e96284010004f77644010006b56444010006d56344010005e47244010006e56244010004fb7644010006e96244010
  | 1 => 0x8020006e56148020004fb7648020006f16148020004de7319710004dd73197100047e75d93100047d75d9310004de73d9310004dd73d9310004ee7299310004ed72993100047f75593100047c75593100055d73153100057970153100047e7598f100047d7598f10004ee7298f10004ed7298f100047e7518f100047d7518f100065e6354f100065d6354f100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b10005d5739071000755534c710006e462487100055d73d4310004de7399610004dd73996100055d739961000c7e74996100065e73996100047d73996100065d73996100045d739961000c7c74596100047f73596100047e75d92100047d75d92100047f75592100047c7559210004df7359210004dc73592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed721921000c7f76952100047d769521000c7f76152100047d76152100055d73152100057970152100047e75d8e100047d75d8e100047e7598e100047d7598e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e100047f76d4e100047d76d4e100047f7654e100047d7654e100065f6354e100065c6354e100047e75d8a100047d75d8a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a10006e76208610005f170086100055d73d4210007e02188210005f07148210007e32148210004de7399510004dd7399510004ee7299510004ed7299510004ef7259510004ec72595100047e75d91100047d75d9110004ee7299110004ed72991100047f75591100047c7559110004df7359110004dc7359110004ef7259110004ec72591100055d73151100057970151100047e7598d100047d7598d10004ee7298d10004ed7298d10004ef7258d10004ec7258d100047e7518d100047d7518d100065f6354d100065c6354d100066e54d89100066c54d89100066f53d89100066d53d8910004ee7298910004f771589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd7318910004ee76189100066e75189100066d7518910006ae7418910006ad74189100066e54189100066c5418910006ce7318910006cd73189100066f53189100066d5318910006e57118910006e97018910005d57390510006e46290510004f47650510006e46250510006e4628c510004f4764c51000755534c510006e4624c510004f67688510006e46288510004f47648510006e462485100055d73d41100066f62d41100066c62d41100066f62541100066c6254110006e86288110007e22188110004f87648110007e12148110006e46284110004be74d9410004bd74d9410004de73d9410004dd73d9410004e
  | 2 => 0x6765418520006745418520006d67318520006d57318520006775318520006755318520006e64218520006e54218520006e63218520006e53218520006f17018520004ee76c8520006e461c8520006e461485200055d73d41200067761d41200067461d4120006776154120006746154120006e46188120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d769942000c7e74994200047d739942000c7c74594200047f73594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d9020004bd76990200063e65990200063d659902000e3f759902000e3c75990200047f75590200047c75590200063e65590200063d65590200063f75590200063c75590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f5711902000c7f76950200047d769502000e3e64950200063d649502000c7f76150200047d761502000e3e64150200063d64150200055d73150200057970150200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c200047e7598c200047d7598c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c200065e7598c200065d7598c200065e5498c200065c5498c200065e6558c200065d6558c200069e6458c200069d6458c200065e7558c200065d7558c200065e5458c200065c5458c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c200047f76d4c200047d76d4c200063e64d4c200063d64d4c200065e63d4c200065d63d4c200047f7654c200047d7654c200063e6454c200063d6454c200065e6354c200065d6354c20006766598420006756598420006b66498420006b56498420006d66398420006d56398420006765498420006745498420006775398420006755398420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006765458420006745458420006775358420006755358420004ed7688420006ad6488420006cd6388420006e56188420006ad6408420006cd6308420006e56108420005e970084200047e75980200047d75980200047d76d40200063e64d40200063d64d40200055d73d40200065e63d40200065d63d40200067661d40200067561d40200047f76540200063e64540200063d64540200065e63540200065d6354020006766154020006756154020006ad64c8020006cd63c8020006e561c8020006f16188020004ef7648020006ad6448020006cd6348020005e4714
  | 3 => 0x56498430007555398430006e66298430006e562984300067654984300067454984300067753984300067553984300065d5358430006766558430006756558430006b66458430006b56458430007555358430006e66258430006e56258430006765458430006745458430006775358430006d65358430006755358430006d55358430006555358430006d74358430006d443584300047e75980300047d75980300065d53980300047d76d40300063e64d40300063d64d40300055d73d40300066e62d40300066d62d40300067661d40300067561d40300047f76540300063e64540300063d64540300066e62540300066d62540300067661540300067561540300055d75cc0300069d64cc030006cd62cc030006d561cc030006b9648c03000759538c030004df764c0300055d754c0300069d644c030006cd624c030006d5614c030004fb764c030006b9644c030004de7319720004dd73197200047e75d93200047d75d9320004de73d9320004dd73d9320004f67199320004f571993200047f75593200047c75593200055d73153200057970153200047e7598f200047d7598f20004f67198f20004f57198f200047e7518f200047d7518f200065e6354f200065d6354f20005cd7390b200074d534cb200055d73d4320004de7399620004dd73996200055d739962000c7e74996200065e73996200047d73996200065d73996200045d739962000c7c74596200047f73596200047e75d92200047d75d92200047f75592200047c7559220004df7359220004dc73592200047e75192200047d7519220004de7319220004dd7319220004f67119220004f5711922000c7f76952200047d769522000c7f76152200047d76152200055d73152200057970152200047e75d8e200047d75d8e200047e7598e200047d7598e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e200047f76d4e200047d76d4e200047f7654e200047d7654e200065f6354e200065c6354e20005e970086200055d73d4220004de7399520004dd7399520004f67199520004f57199520004f77159520004f471595200047e75d91200047d75d9120004f67199120004f571991200047f75591200047c7559120004df7359120004dc7359120004f77159120004f471591200055d73151200057970151200047e7598d200047d7598d20004f67198d20004f57198d20004f77158d20004f47158d200047e7518d200047d7518d200065f6354d200065c6354d20005cd7390920004ec7650920004ec764c9200074d534c9200067654d85200067454d85200067753d85200067553d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd7318520006767518520006757518520006b67418520006b57418520
  | 4 => 0x953000c7c74595300063c74595300043c74595300047f73595300065f73595300047f70595300067b70595300047e75d91300047d75d91300047f75591300047c7559130004df73591300047e75191300047d7519130004ee7219130004ed7219130004f67119130004f5711913000c7f76951300047d76951300055d739513000579709513000c7f76151300047d76151300063f641513000e3c64151300055d73151300057970151300057970d4d300057b7054d30004de7690d300065d6590d30004dc7650d300065d6550d300069c6450d300047e75d89300047d75d89300047e75189300047d75189300065d65cc930005d571cc9300065d654c9300047e75d85300047d75d85300047e75185300047d75185300065d65cc530005cd72cc5300065d654c5300055d73d41300047f76541300047d76541300055f7354130006796590130004f876501300067965501300079943501300065d658c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d769943000c7e74994300065e739943000c7c74594300047f73594300047d73594300047e7519430004be7419430004bd7419430004ee7219430004ed7219430004f67119430004f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d659903000e3f759903000e3c75990300047f75590300047c75590300063e65590300063d65590300063f75590300063c75590300069c73590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f57119030004fa701903000c7f76950300047d769503000e3e64950300063d649503000c7f76150300047d761503000e3e64150300063d64150300055d73150300057970150300047e7598c300047d7598c300047d76d4c300063e64d4c300063d64d4c30004dd7694c300055d7594c300069d6494c300047f7654c300063e6454c300063d6454c300065e6554c300069d6454c300055f7654c300065f7654c300055c7454c300065f6454c300071e6454c300065d6454c300071d6454c300061d6454c300055f7054c30004dd76d0c300055f75d0c300069d64d0c30004dd7610c300055d7510c300069d6410c30005d97010c300066e65988300066d6598830006ae6498830006ad64988300074d53988300066e54988300066c54988300066f53988300066d53988300065d53588300066e65588300066d6558830006ae6458830006ad64588300074d53588300066e54588300066c54588300066f5358830006ce53588300066d5358830006cd53588300064d5358830006cf4358830006cc4358830006766598430006756598430006b66498430006b
  | 5 => 0x65d6558c400065e7558c400065d7558c4000e5e5458c4000e5c5458c400047f76d4c400047d76d4c400065e63d4c400065d63d4c400047f7654c400047d7654c4000d3c7454c400065e6354c400065d6354c400066e65988400066d6598840006ce6398840006cd639884000e6e549884000e6c54988400066f53988400066d53988400066e65588400066d6558840006ce6358840006cd635884000e6e545884000e6c54588400066f53588400066d5358840006766598440006756598440006d66398440006d56398440006e66298440006e5629844000e76549844000e745498440006775398440006755398440006766558440006756558440006d66358440006d56358440006e66258440006e5625844000e76545844000e7454584400067753584400067553584400047e75980400047d75980400047d76d40400055d73d40400065e63d40400065d63d40400066e62d40400066d62d40400067661d40400067561d40400047f76540400065e63540400065d63540400066e62540400066d62540400067661540400067561540400067a60540400069d63d0040006ad62d0040006b561d0040006796590040006d96390040004bf76500400069d6350040006ad6250040006b56150040007395050040004fb765004000679655004000f3a5450040006d9635004000c7e749973000c7c74597300047e75d93300047d75d93300047f75593300047c75593300047e75193300047d7519330004ee7219330004ed7219330004f67119330004f5711933000c7f76953300047d76953300055d739533000c7f76153300047d76153300055d73153300057970153300065d6590f300065d6550f300069c6450f300065d65ccb30005d571ccb300065d654cb300065d65cc730005cd72cc7300065d654c7300055d73d43300055f735433000c7e74996300065d739963000c7c74596300047e75d92300047d75d92300047f75592300047c75592300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f5711923000c7f76952300047d769523000579709523000c7f76152300047d76152300055d73152300057970152300057970d4e300065e6594e300057b7054e300065f7654e300065c7654e300055c7454e300065f6454e300065d6454e300055f7054e300075b7054e30007587054e300055f75d0e300055d7510e30005d97010e300065d5358a30004f77158a30004f47158a300065d5358630004ef7258630004ec72586300055d73d4230006796590230007595390230006796550230005d873502300075953502300079b43502300055d75cc230004dd739953000c7e74995300047d73995300065d73995300045d73995300047d7099530006797099530004bf7459530004bc74595300053c74595300063f745
  | 6 => 0x5711974000e7970197400047e7598f400047d7598f400047f7558f400047c7558f4000c7e76d4f4000c7c7654f400065e6354f400065d6354f400071d5350f400047e7598b400047d7598b40004de7398b40004dd7398b400047f7558b400047c7558b40005b571d0b400047e75987400047d7598740004de7398740004dd73987400047f75587400047c7558740005ad72d074000d3e74d43400055d73d434000d3c7454340004de7399640004dd73996400055d73996400065e73996400047d73996400065d73996400045d73996400067a70996400047f73596400055d73152400057970152400047e7598e400047d7598e400047f76d4e400047d76d4e400057970d4e400047f7654e400047d7654e400053c7454e40004f77158a40004f47158a40004ef7258640004ec72586400055d73d42400067a65542400057b76542400067b765424000d7874542400057b73542400073950d024000d7b75d024000f3a54d02400047d73d95400047e7599540004de7399540004dd7399540004df7359540004dc73595400047e761954000c7e741954000c7c74195400047d73195400067970195400047e76951400047e76151400055d73151400065f65d8d400065c65d8d400065f75d8d400065c75d8d400065e54d8d400065c54d8d400047e7518d400047d7518d40004ee7218d40004ed7218d40004f67118d40004f57118d400065f6518d400065c6518d400065e7518d400065d7518d400065e5418d400065c5418d40006ce7218d40006cd7218d40006d67118d40006d57118d40006d97018d400047e76d4d400047c76d4d400065f63d4d400065c63d4d400057970d4d400047e7654d400047c7654d400065f6354d400065c6354d400069c63d0d400069c6350d400071d5350d40005b571d0940005ad72d05400047e76d41400053e74d41400055d73d41400065f63d41400065c63d41400057975941400067865941400047c76541400053c74541400065f63541400065c6354140004f876541400067b76541400057876541400067876541400047876541400073b745414000d7874541400073874541400057b73541400075b63541400075863541400073b43541400073943541400073b42541400073942541400073b415414000739415414000d7b75d0140007395090140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d769944000c7e74994400047d739944000c7c74594400047f73594400047e7519440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f57119440004fa701944000c7f759904000c7c75990400047e7598c400047d7598c400065e6598c400065d6598c400065e7598c400065d7598c4000e5e5498c4000e5c5498c400065e6558c40
  | 7 => 0x52500057970152500065d6354e500055d73d4250004de7319150004dd7319150004ee7219150004ed7219150004f67119150004f571191500047e76d51500063f649515000e3c64951500057a70951500055e73151500055d73151500056e72151500056d72151500057671151500057571151500057a70151500065f6394d500065f6354d500065c6354d500047e7614d50004de7318950004dd73189500055e73149500055d7314950004de7318550004dd73185500055e73145500055d73145500063f64991500057970991500055f73591500055c73591500057b70591500055e73191500055d73191500056e72191500056d721915000576711915000575711915000e5e73191500047d731915000e5d73191500045d731915000e6e721915000e6d721915000e76711915000e75711915000e79701915000c7e74d8d500065f6398d50005797098d500053f7458d500053c7458d500057b7058d500065d6318d5000c7c76d0d500065f63d0d500057a70d0d500057970d0d500047e7690d500047d7690d500063c6490d500047f7650d500047c7650d500047e7610d500047d7610d5000e3c6410d500065f6310d500071d4310d500056e7210d500056d7210d50005767110d50005757110d500057a7010d50005797010d500057970989500057771589500057471589500057b70589500055e73189500055d73189500057671d09500057571d09500057a70d09500057970d09500047e76909500047d76909500055e73909500055d73909500047f76509500047c76509500057a70109500057970109500047e76cc9500047d76cc9500057671cc9500057571cc9500047e760c9500047d760c9500057970985500056f72585500056c72585500057b70585500055e73185500055d73185500056e72d05500056d72d05500057a70d05500057970d05500047e76905500047d76905500055e73905500055d73905500047f76505500047c76505500057a70105500057970105500047e76cc5500047d76cc5500056e72cc5500056d72cc5500047e760c5500047d760c5500047e76085500047d76085500053e74085500053d74085500055e73085500055d73085500076521085500057a70085500057970085500055e73d81500055d73d81500057974d81500075a73d81500075973d81500065e73994500065d73994500047d769505000e3e64150500055d73150500057970150500065d63d4c500047f7654c500055d73d40500047f7654050004fb76540500067a655405000e3e74d97400047d73d974000e7970d9740004de7319740004dd7319740004ee7219740004ed7219740004f67119740004f5711974000e3e741974000e5e73197400047d731974000e5d73197400045d731974000e6e721974000e6d721974000e76711974000e7
  | 8 => 0x55d73153500056e72153500056d72153500057671153500057571153500057a70153500065e5498f500065c5498f500065e7558f500065f5458f500065e5458f500065d5458f500065c5458f500065e63d4f500065d63d4f500065d6394f500065e6354f500065d6314f500065d63d4b500065d6394b500065d6354b500055e7314b500055d7314b500065d6314b500065d63d47500065d63947500065d63547500055e73147500055d73147500065d63147500055e73d93500055d73d93500057970d93500063f64993500047d73993500055e73193500055d73193500056e72193500056d72193500057671193500057571193500057970193500057970d8f500065f6398f500065e6498f500065c6498f5000c7c7458f500065f7658f500065f6458f500065e6458f500065d6458f500065c6458f500065f7458f500065e7458f500065d7458f500065c7458f500065f7258f500065e7258f500065d7258f500065c7258f500065f7158f500065e7158f500065d7158f500065c7158f500065f7058f500065d7058f500065d6318f50005797018f5000c7f76d0f500065d63d0f500047e7690f500047d7690f500065d6390f500047f7650f500047c7650f500065d6350f500047e7610f500047d7610f500065d6310f500071d4310f500056e7210f500056d7210f50005767110f50005757110f500057a7010f50005797010f500055e73d8b500055d73d8b500065d63d8b500057671d8b500057571d8b500057970d8b500065d6398b500065d6358b500055e7318b500055d7318b500065d6318b50005797018b500065d63d0b500057671d0b500057571d0b500047e7690b500047d7690b500055e7390b500055d7390b500065d6390b500047f7650b500047c7650b500065d6350b500065d6310b500047e76ccb500047d76ccb500065d63ccb500057671ccb500057571ccb500065d638cb500065d634cb500047e760cb500047d760cb500065d630cb500055e73d87500055d73d87500065d63d87500056e72d87500056d72d87500057970d87500065d63987500065d63587500055e73187500055d73187500065d63187500057970187500065d63d07500056e72d07500056d72d07500047e76907500047d76907500055e73907500055d73907500065d63907500047f76507500047c76507500065d63507500065d63107500047e76cc7500047d76cc7500065d63cc7500056e72cc7500056d72cc7500065d638c7500065d634c7500047e760c7500047d760c7500065d630c7500065d63c87500065d63887500065d63487500047e76087500047d76087500053e74087500053d74087500055e73087500055d73087500065d63087500076521087500057a700875000579700875000e3e64952500063d64952500057970952500055d731
  | 9 => 0xd76990210063e65990210063d659902100e3f759902100e3c7599021006ae7299021006b671990210047f75590210047c75590210063e65590210063d65590210063f75590210063c75590210047e75190210047d7519021004be7419021004de7319021004dd7319021004fa7019021004f9701902100c7f76950210047d769502100e3e64950210063d649502100c7f76150210047d761502100e3e64150210063d64150210055d73150210057970150210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c210047e7598c210047d7598c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c210065e7598c210065d7598c210065e5498c210065c5498c21006ce7298c21006d67198c210065e6558c210065d6558c210069e6458c210069d6458c210065e7558c210065d7558c210065e5458c210065c5458c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004fa7018c21004f97018c210047f76d4c210047d76d4c210063e64d4c210063d64d4c210065e63d4c210065d63d4c210047f7654c210047d7654c210063e6454c210063d6454c210065e6354c210065d6354c21004ed76908210066d6590821005cd7390821006cd6390821005e571908210066d6550821006ae6450821006cd6350821004ed768c821006ad648c821005e5718c821006ad644c821006ce634c8210074d534c821004f57690421006756590421005d57390421006d56390421005e57290421006756550421006b66450421006d56350421007a54250421004f5768c421006b5648c421005e5728c421006b5644c421006d6634c42100755534c421007c5324c421005e57288421004ef7648421004f77648421005e77648421006e77648421007666548421007656548421005e77448421005e57448421007a66448421007a56448421007665448421007645448421005e77348421005e57348421007c66348421007c56348421007675348421007655348421005e470484210047e75980210047d75980210067a6598021006796598021006ba6498021006b96498021006da6398021006d96398021007e121980210067a75980210067975980210067a54980210067854980210067b5398021006795398021006e521580210067a6558021006796558021006ba6458021006b96458021006da6358021006d96358021007e121580210067a75580210067975580210067a54580210067854580210067b5358021006795358021006ea4258021006e94258021006ea3258021006e93258021006f24158021006f14158021006f23158021006f13158021006eb2158021006f22158021006e92158021006f12158021006e121580210063e64d535000e3e64153500055e7315350
  | 10 => 0x82310047e75d91310047d75d9131004ee7299131004ed72991310047f75591310047c75591310055d73151310057970151310055d7594d31004dc7654d310065f7654d310065c7654d310055c7454d310065f6454d310065d6454d31007577154d31007547154d310055f7054d31004de76d0d310055f75d0d310055d7510d31005cd7210d31005d67110d31005d97010d310065d53d89310047e75189310047d75189310055d75cc931005d671cc931005d67390531007555390531004f476505310075553505310075553cc531005e672cc5310047e75181310047d7518131004be7418131004bd74181310065d5318131004ee7218131004ed72181310047d769943100c7e74994310047d709943100c7c74594310047f70594310047e7519431004de73194310047e75d90310047d75d9031004de73d90310047f75590310047c75590310047e75190310047d7519031004ee7219031004ed7219031004f67119031004fa7019031004f9701903100c7f76950310047d769503100c7f76150310047d76150310055d73150310057970150310047e7598c310047d7598c310047d76d4c310047f7654c310065e6354c310065d65cc431004df764c4310065d654c431004f7764c4310047e75980310047d7598031004de7319721004dd73197210047e75d93210047d75d9321004de73d9321004dd73d93210047f75593210047c75593210055d73153210057970153210047e7598f210047d7598f210047e7518f210047d7518f210065e6354f210065d6354f21005d5739072100755534c7210047e75983210047d7598321004de7319621004dd73196210047e75d92210047d75d9221004de73d9221004dd73d92210047f75592210047c75592210055d73152210057970152210047e7598e210047d7598e210047e7518e210047d7518e210065e6354e210065d6354e21005cd7390a210074d534ca210047e75982210047d7598221004de7319521004dd73195210047e75d91210047d75d9121004de73d9121004dd73d9121004ed7299121004f571991210047f75591210047c75591210055d73151210057970151210047e7598d210047d7598d21004ed7298d21004f57198d210047e7518d210047d7518d210065e6354d210065d6354d210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d769942100c7e74994210047d73994210047d709942100c7c74594210047f73594210047f70594210047e7519421004be7419421004bd7419421004de7319421004dd7319421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d9021004b
  | 11 => 0x47f73596410047f7059641004de7319641004dd73196410055d73152410057970152410047e7598e410047d7598e41004ee7298e41004ed7298e410065e6598e410065d6598e410065e7598e410065d7598e410065e5498e410065c5498e41006ce7298e41006cd7298e41006d67198e410065e6558e410065d6558e410065e7558e410065d7558e410065e5458e410065c5458e410047f76d4e410047d76d4e410065e63d4e410065d63d4e410047f7654e410047d7654e410065e6354e410065d6354e4100676655464100f3654d0641005e672d06410047e75982410047d75982410047d73d95410047d70d95410047e7599541004de7319541004dd73195410047e76195410055d73195410065e73195410047d73195410065d73195410045d73195410067571195410047d70195410047e76951410047e76151410055d73151410057970151410047e7518d410047d7518d410047e76d4d410047c76d4d410047e7654d410047c7654d410053c7454d41005b671d0941006746594541004f47654541005e672d05410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed7218141004de7319441004dd7319441004ee7219441004ed7219441004f67119441004fa7019441004f970194410047e7598c410047d7598c410065e6354c410065d6354c410047e75984410047d7598441004bf7650441004f7765044100f3654504410047e75980410047d7598041004ee72d9731004ed72d973100c7e74997310065e73997310047d709973100c7c74597310047f7059731004ee7219731004ed72197310047e75d93310047d75d9331004ee72d9331004ed72d93310047f75593310047c75593310047e75193310047d7519331004ee7219331004ed7219331004fa7019331004f9701933100c7f76953310047d769533100c7f76153310047d76153310055d73153310057970153310065e6554f310055f7654f310065f7654f310055c7454f310065f6454f310065d6454f310055f7054f310055f75d0f310055d7510f310069d6410f31005cd7210f31005d97010f310066e6598b310066d6598b310074d5398b310066e5498b310066c5498b310066f5398b310066d5398b310065d5358b310066e6558b310066d6558b310074d5358b310066e5458b310066c5458b310066f5358b31006ce5358b310066d5358b31006cd5358b310064d5358b31006cf4358b31006cc4358b310055d75ccb310065d65ccb310065d654cb31006ce624cb310047e75983310047d75983310065d5398331004be74d9631004bd74d96310047e75d92310047d75d9231004ee7299231004ed72992310047f75592310047c755923100e3e64152310063d64152310055d7315231005797015231005e672cc6310047e75982310047d759
  | 12 => 0xe74d9632004bd74d96320047e75d92320047d75d9232004f67199232004f571992320047f75592320047c755923200e3e64152320063d64152320055d73152320057970152320074d53cca32005e671cca320047e75982320047d75982320047e75d91320047d75d9132004f67199132004f571991320047f75591320047c75591320055d73151320057970151320055d7594d32004dc7654d320065f7654d320065c7654d320055c7454d320065f6454d320065d6454d320074f7254d320074c7254d320055f7054d32004de76d0d320055f75d0d320055d7510d32005ce7210d32005d57110d32005d97010d32005ce73909320074d5390932004ec76509320074d53509320074d53cc932005e671cc9320065d53d85320047e75185320047d75185320047e75181320047d7518132004be7418132004bd74181320065d5318132004f67118132004f571181320047d769943200c7e74994320047d709943200c7c74594320047f70594320047e7519432004de73194320047e75d90320047d75d9032004de73d90320047f75590320047c75590320047e75190320047d7519032004ee7219032004f67119032004f57119032004fa7019032004f9701903200c7f76950320047d769503200c7f76150320047d76150320055d73150320057970150320047e7598c320047d7598c320047d76d4c320047f7654c320065e6354c320065d65cc832004df764c8320065d654c832004ef764c8320047e75980320047d759803200e3e64153510055d73153510056d72153510057671153510057970153510065d63d4f51004ee7299251004ed729925100e3e64952510063d64952510057571952510055d73152510057571152510057970152510065e6354e510065d6354e510063f649515100e3c64951510057671951510055d73151510056d72151510057671151510057970151510065f6354d51004de7318951004dd731895100e3e64150510055d73150510057571150510057970150510065e5498c510065c5498c510065e7558c510065e5458c510065c5458c510065e63d4c510065d63d4c510065e6354c510065d63d44510047f76544510065d6354451004f77654451004ee72d9741004ed72d9741004de7319741004dd7319741004ee7219741004ed7219741004fa7019741004f970197410047e7598f410047d7598f4100d3c7454f410065e6354f410065d6354f410047e7598b410047d7598b41004de7398b41004dd7398b410066e7598b410066d7598b4100e6e5498b4100e6c5498b41006ce7398b41006cd7398b410066f5398b410066d5398b4100e6e5458b4100e6c5458b410066f5358b410066d5358b41006ae6250b410047e75983410047d7598341004de73d9641004dd73d96410047d73996410067671996410047d7099641
  | 13 => 0x874200676759874200675759874200e76549874200e745498742006d67398742006d5739874200677539874200675539874200e76545874200e7454587420067753587420067553587420047e75983420047d7598342004de73d9642004dd73d96420047d73996420066e72996420047d70996420047f73596420047f7059642004de7319642004dd73196420055d73152420057970152420047e7598e420047d7598e42004f67198e42004f57198e420065e6598e420065d6598e420065e7598e420065d7598e420065e5498e420065c5498e42006ce7298e42006d67198e42006d57198e420065e6558e420065d6558e420065e7558e420065d7558e420065e5458e420065c5458e420047f76d4e420047d76d4e420065e63d4e420065d63d4e420047f7654e420047d7654e420065e6354e420065d6354e420066e6554a4200f2e54d0a42005e671d0a420047e75982420047d75982420047d73d95420047d70d95420047e7599542004de7319542004dd73195420047e76195420055d73195420065e73195420047d73195420065d73195420045d73195420066d72195420047d70195420047e76951420047e76151420055d73151420057970151420047e7518d420047d7518d420047e76d4d420047c76d4d420047e7654d420047c7654d420053c7454d420066c6594942004ec7654942005e671d09420047e75181420047d7518142004de7318142004dd7318142004f67118142004f57118142004de7319442004dd7319442004ee7219442004f67119442004f57119442004fa7019442004f970194420047e7598c420047d7598c420065e6354c420065d6354c420047e75988420047d7598842004bf7650842004ef765084200f2e54508420047e75980420047d7598042004f671d9732004f571d973200c7e74997320065e73997320047d709973200c7c74597320047f7059732004f67119732004f571197320047e75d93320047d75d9332004f671d9332004f571d93320047f75593320047c75593320047e75193320047d7519332004f67119332004f57119332004fa7019332004f9701933200c7f76953320047d769533200c7f76153320047d76153320055d73153320057970153320065e6554f320055f7654f320065f7654f320055c7454f320065f6454f320065d6454f320055f7054f320055f75d0f320055d7510f320069d6410f32005d57110f32005d97010f320067665987320067565987320075553987320067654987320067454987320067753987320067553987320065d5358732006766558732006756558732007555358732006765458732006745458732006775358732006d65358732006755358732006d55358732006555358732006d74358732006d443587320047e75983320047d75983320065d5398332004b
  | 14 => 0x65d5318143004ee7218143004ed7218143004f67118143004f57118143004ee72d9443004ed72d9443004f671d9443004f571d9443004fa70d9443004f970d94430047d769944300c7e74994430047d709944300c7c74594430047f70594430047e7519443004de7319443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f9701944300c7f759904300c7c75990430047e7598c430047d7598c430047d76d4c430047f7654c430065e6354c430065d6590c430059d7490c43004bf7650c430071f5350c430071d5350c43004df7650c430065d6550c4300f1e5450c4300f1c5450c430059f7650c430069f7650c430071f7550c430071c7550c430071e6550c430071d6550c430066e65988430066d65988430078d439884300e6e549884300e6c54988430066f53988430066d53988430066e65588430066d65588430078d435884300e6e545884300e6c54588430066f53588430066d5358843006766598443006756598443007954398443006e66298443006e5629844300e76549844300e745498443006775398443006755398443006766558443006756558443007954358443006e66258443006e5625844300e76545844300e7454584430067753584430067553584430047e75980430047d75980430067a6598043006796598043007994398043006ea6298043006e96298043006f26198043006f161980430067a759804300679759804300e7a549804300e7854980430067b53980430067953980430069d43580430067a6558043006796558043007994358043006ea6258043006e96258043006f26158043006f161580430067a755804300679755804300e7a545804300e7854580430067b5358043006795358043006bb4358043006da4358043006b94358043006d9435804300699435804300e3e64153520055d73153520056e72153520057571153520057970153520065d63d4f52004f67199252004f5719925200e3e64952520063d64952520056d72952520055d73152520056d72152520057970152520065e6354e520065d6354e520063f649515200e3c64951520056e72951520055d73151520056e72151520057571151520057970151520065f6354d52004de7318552004dd731855200e3e64150520055d73150520056d72150520057970150520065e5498c520065c5498c520065e7558c520065e5458c520065c5458c520065e63d4c520065d63d4c520065e6354c520065d63d48520047f76548520065d6354852004ef7654852004f671d9742004f571d9742004de7319742004dd7319742004f67119742004f57119742004fa7019742004f970197420047e7598f420047d7598f4200d3c7454f420065e6354f420065d6354f420047e75987420047d7598742004de7398742004dd739
  | 15 => 0x842580540067b71580540067a715805400679715805400678715805400e7b415805400e7841580540063e64d535300e3e64153530055e73153530056e72153530056d72153530057671153530057571153530057a70153530057970153530055d73d93530063f64993530047d70993530055d73193530056e72193530056d72193530057671193530057571193530057a701935300579701935300c7c745835300e3e64952530063d64952530055d73952530055d7315253005797015253004ee7219153004ed7219153004f67119153004f57119153004fa7019153004f970191530047e76d51530063f649515300e3c64951530055e73951530055e73151530056e72151530056d72151530057671151530057571151530057a70151530057970151530063f64991530055d73991530055f73591530056e72191530056d72191530057671191530057571191530057a701915300579701915300e5d731915300e6e721915300e6d721915300e76711915300e75711915300e7a70191530047d701915300e7970191530047970191530055d74d8d530055d72d8d530055d71d8d530055e70d8d530053e74989530053d74989530053e74985530053d749855300c7e74d81530053f74581530053c74581530047d769505300e3e64150530055d73150530057970150530047f7654c53004df7654c530065e6554c5300e3e74d974300e5d73d97430047d70d9743004ee7219743004ed7219743004f67119743004f57119743004fa7019743004f9701974300e3e741974300e5d731974300e6e721974300e6d721974300e76711974300e75711974300e7a70197430047d701974300e79701974300479701974300d3e74d4f4300d3c7454f430047e7598b430047d7598b430047f7558b430047c7558b430047e75987430047d75987430047f75587430047c75587430047e75983430047d75983430047f75583430047c75583430065e73996430047d70996430047f70596430055d73152430057970152430065e6554e430055f7654e430065f7654e4300d5c7454e430055f7054e430071d53d0e4300d5f75d0e4300f1e54d0e430065d5358a430065d53586430047e75982430047d75982430065d53982430047d70d95430047e75995430047e76195430065d73195430047d70195430047e76951430047e76151430057970151430047e76d4d430053e74d4d430055d7594d430065c6594d430047c7654d430053c7454d43004dc7654d430059c7454d430065f7654d430055c7654d430065c7654d430045c7654d430071f7454d4300d5c7454d430071c7454d430051c7454d430055f7054d4300d5f75d0d430071d5390d430065d53d8943004f671d8943004f571d89430065d53d8543004ee72d8543004ed72d85430047e75181430047d7518143
  | 16 => 0x8054006e96298054006f26198054006f16198054006da6358054006d96358054006ea6258054006e96258054006f26158054006f161580540067a75580540067b545805400679545805400e3e749905400e5f6398c5400d5d7698c5400e5e6498c5400f1e6498c5400e5f6098c5400e5c6358c5400e5f4358c5400e5c4358c540047f7058c5400d5f7658c540065f7658c5400e5e6458c5400f1e6458c5400e5f6258c5400e5c6258c5400e5f6158c5400e5c6158c5400e5f6058c5400e5c6058c5400e5e7458c540065f7258c540065e7258c540065d7258c540065c7258c5400e5f4258c5400e5c4258c540065f7158c540065e7158c540065d7158c540065c7158c5400e5f4158c5400e5c4158c540065f7058c540065e7058c540065d7058c540065c7058c5400e5f4058c5400e5c4058c540065d639885400e6f629885400d6d769885400e6e649885400f2e649885400e6f639885400f4e63988540066d639885400f4d63988540064d639885400e6f60988540065d635885400e6c625885400d6f76588540066f765885400e6e645885400f2e645885400e6f635885400f4e63588540066d635885400f4d63588540064d635885400e6f615885400e6f60588540065d639845400e77619845400d75769845400e76649845400f36649845400e77639845400f56639845400675639845400f55639845400655639845400f66629845400f65629845400e7760984540065d63584540066d625845400e74615845400d77765845400677765845400e76645845400f36645845400e77635845400f56635845400675635845400f55635845400655635845400e77625845400f66625845400675625845400f65625845400665625845400e7760584540065d639805400e7b609805400d79769805400e7a649805400f3a649805400e7b639805400f5a639805400679639805400f59639805400659639805400f6a629805400f69629805400f72619805400f7161980540065e63580540065d63580540066e62580540066d625805400676615805400675615805400e7860580540047f735805400e7b405805400e78405805400d7b76580540067b765805400e7a645805400f3a645805400e7b63580540067a635805400f5a63580540065a635805400679635805400f59635805400659635805400e78635805400e7b62580540067a625805400f6a62580540066a625805400679625805400f69625805400669625805400e78625805400e7b61580540067a615805400f72615805400672615805400679615805400f71615805400671615805400e78615805400e7a74580540067b73580540067a735805400679735805400678735805400e7b435805400e7843580540067b72580540067a725805400679725805400678725805400e7b425805400e7
  | 17 => 0x300100300202c00100201500000200000100001600100100800201000a01100d00b00700501600001600300500700001000600c00000700300000000100500000301300004e02d01400000000a00b00400101300b00102400000300100700700700000d00100000300000600401400200501201200400000700d00000001801804400100c00002800202c01d00201a04200400600e00200f00200200f00500d00300700000c00400c01c01301e00505000100100b01700b00000000000000800c00000301000400000000000e00600600f01800300000001d00100000601500004601601000900301000200400000000400101100f00a00000c00a01c02600600500200200800100500200f00000400202000700900000001f00000101100000000000200001a00700000000000100d05201700600002b00001000400100300100700501001e01b00300000b00b00100300400200001202300201400500a00104b00200400200a00000201200500500800a00602100700600000700000400100001900000000000801100100001600100d00000000100100001900700100600000f00200002c00400900000000200001a00800401300f00700300200100201901d00400100600000902000002400000300000100001500003600100100300000200200103f00100e00001801d00700c00600000000900100100d00800000001700100100000300c00600100400900d01e00000300600000700001900600400300700000500000000000400300000000000301b00001000900600600600f02600902e00002501800500100300000500300100100700800100200500a00000300b01500e00a02300500000801600000600000800900000000000000300d00a00100200600200003800400100000000000d02f03300c00000000700800000000000400400000000b00d01300100e01000001900100400000100100501801f00300001e01f0070053d76d52540063d76d5254004de7398a54004dd7398a54004de7398654004dd7398654004df7358254004dc735825400e5f6398e5400e5c6358e5400e5f4358e5400e5c4358e540047f7058e540055e7398a540055d7398a5400e6f6298a5400e6c6258a540055e73986540055d739865400e77619865400e74615865400e7b60982540055f73582540055c735825400e7860582540047f73582540065f73582540045f73582540065c735825400e7b405825400e7840582540063e65950540047f7655054004bf76550540065e7558c540065f5458c540065d5458c54006ce6398854006cd6398854006ce6358854006cd6358854006d66398454006d56398454006e66298454006e56298454006d66358454006d56358454006e66258454006e56258454006da6398054006d96398054006ea629
  | 18 => 0x800048702f9c043e07de0a191e0b3e2a713800000009e04f823d88c684b3e582941aeb3b16388944b47f85761c7500c0003fd00015604a203aaaa0b5e5720000dc0fee5dc0000bd440680a0000de4b4800000000005ca34d1ad2954f9400000007d8000285000000022e36509d18102f448426d80016925f3000245489aafa0e600005448d00e2a68d6e490e3578360a4e1af4ea28547dc86457882e549c5423bb92e00004134d228486469991f61380f1c1b31da83580006f533916815e00002bea8b40004fa0b399dc0000003720e4d150a590409da967e76e3be93305660132bd8c340009492968428000aba0001f040ee98300000004d695453386643442713c1800129400000801400400100300000900e00f00300701f05500000100900a02001100000200101001a00901501800000400601900002c00002500101100400401202300100800000300000000e00d00b02000f00302700900700100300701b00c00400c02c04600000000600000200b00300000000800200b00a02500b00d00101200106a00000400000000000b00000100600100300500500004402201300800301400600400200000d00001201700d00601900500701b01b02700300000900006500000a00200600000101a00100500300100200300500105200000300001800100900c00001900100800000000100000000c02b01406100201004001500700300100100000d00501000600b02800000100900700001f00000400100400101000000000f01400700000600d00003900600000300601200000401201b00000700000200500400001701400000400000d00700000c00301500402400000c01500c00200700301200200302900000200000000100000600200000100600101300200a00300002a00701700000201d00900000200b00000400700201100100a01701400601700900200300101100e00800004201b00000e00c00100000900100200400200b00100700000500000d00000000800700000100300503d00700200c00303900700400b00900000000000000600000100700300000100300f00700000000b00000000102300503900602100000f00100400900300200100400900004400300200a00001f03100100002000500600200500000300600000000400000200900305f00c00202000000d00100201600200502e00200000700400000201c00200f00a01900200f00e01d00000000502a00300000f00302100901800100c00000701f00000d00c06f00901200600102409800102500501b00c00200202a00200100000900400a00a01b00000001c00a00009100000000600300900400900000300302500701602b00d00402400102a00101100800900200200000000f00500600000100401300200003500a00b004008026008000004018002001000000
  | 19 => 0x2450f9cb949db026900867226019a0244000b25000264800016327a800028879a2e700000a67b8387201d63aaa524126fc8b005908e1198fda11912f000c69203c32794c155c4860e511fc9b80ca4ca9a6ce5ab6d3c380008c045a03416b830658a57c0954ec6736102a04d5be037004a2f54ec55950426596faa3d50113b4ebe3e2554a5f137279b53287b90085764670f8cca6a3551120d0c5a1ff495142c82236f3659d34000b6e41018d49bc0000c3a58d10013321e2d148740b636a80000003df0e7863437073c546064d548a320158a940cc35d24c80001623350002ac870a8854e780009ee2b6143878d5c41d90002614e428792ee8b0877000053da824000acf0000ea46a42940b9aa704b6b663229f240000d933d81242c095a1c922cc39a8320000000d784690940f6010c0001a225a80004ec3a78ae8fb666e5ab9ec400082500600012d891132a0e5c17ea9635b97900008533de1c640003d91c01e800007115a423c48dc046302a078ea02cb55c1e0966858951c28ec192123488006c000000000078000000034925ad11e00000900000000000002c380008d753f8930b506f435f915c1e41df430a69563253f37c97501faa83136800000010200028446f800000027947ea89e00121744469073920000db416634caa800008140000000c7c0001ba800070416f44690a000099e00021c168e8c358500004587bd00006596c65eb1068680c18ac140ea52c0008ec4e71fd00000000d7219d70c3b91e48e4006c5b336ea81927c9ab17213f46c09bc0b42dcc2a883534724742ea5f01929a208880dc2972dd40fab3655da5990c65da0d398f074481c4c1055d0d066337112bc8082f24b404d816017844a92e53764b6255a33402c17158f9e2d0a40e349f8d647d094d5b50b58cba21d564a7ad11839b13f103c04471054aa9e95ae42754085655361320b29d28ef494e19b9b8089c98826100000661ef2cb884c73a00014b80000000005b89c80a681ab1288f500007391001b38e3e3d055b2378ab605a5a8800007e0003d70a2517400000000003780f330028b0a965180dc8be968c03a013800089e60600019bc61ea5e5421a707080801ca2b4d11006d010a08c7c08e34e51d04f885b41880000fac1d10242c200769e400012f45606401949e90674000165114818c000463102825e6c852327b8982000000000103e0bb3148000466195073000157e000000000000071810780000000003352ca5562897416124492400000008206588993d622ec6226592fb906d1fe55c000287451621f0002b610de8bc286a700c282a30f923ac58a0000001ca4a3492e0002c4400000009ba7240000001521470d1677e00019d845e51922e9d39480a580f8addd19e1c9000070917217f53897316503a70001274000330323000000035400002f
  | 20 => 0x54d624811db80000ca2302739d500006d80000f1c6be67d50e12900003012aea59c0003c10440cb8d56b7f5068c910fe89b565840035885900012b0eb200012290c8f983c34ba86c420a4d34d729752b29f71a002c922c3fe0000000b8c6bb49d0d1865a0001a0892400097b145070d6ec00021480013b08d52019a10846693266a9c00004a1383196049a620095a418ac6aed169a7f0872b0531410a84487004af96f55207511708aa91c854c4fd90712a622728527fcd667070f223044ba7e61281ffcc1e3ba513a03c330b2b5702acceb8b162d6067530009b39c16045b200000005f05c4960327272067c6695790378f1e92849d84f49c234808c00010480a15b003b40002ee0218000df82df0000000222aaf2a000a91e04834ab85040000002e002d0380a7c000076800000032581e8fc600054e8d8516c4260fb962c0000623f095bca6233d4bc9f7cf5237b12b80008be2b95718c6d3b40001541bb0000a330002b7099028007a24212880005ad8ea839c68739a90185b634312a204532e6d92cc87cce143715a1280047660e00028815160000db80015fc3e609a91e900a3fc39297bd5d261506a15a80000001f22c040002c80480000482000247a0880000002f91170f547ec0002cd4ec06de34a1cd0c54074515845097c53628fa81400000019da1e837484338b80000006033362a2527056b23ea1ac0000ef0001f40d9400056929f563400018e8d0933aa4c4aea4888fc37f5af86694c006c04ba04864c76d13a00003d65b9000271c00040c54f1e4c47c926000209cabc8730afae002807f108b0f7809ca0300025c0d749183a4049d6466e558b984d0b043d3a91b406128484fea64c0a86b41ed03fd5883164f19ed14c60002d080011940003d28000052a1b093000000000006616180003c24b6800000066d000000124000000000015582d20000001002000000279cf6000000000015285770002ab49e86e124721d52fe39952ba8945a08d33aeab28eac8c01bb157d4e829a18727e005ab1413923f91d0a7834b253c5ec0f84d4803c49c2e31cf96996d80001d986506321f91e99da0d1a4b00d805781c067a31f83909f075711324643da08413d18e0d6061d1090a80e465370ec1cb045c4701c509fd3b885050b2604e8014d2c189992de0ac5c192a499e5471158c610609553551ccc69621c4b2a24916058d2f307486406c636da3d42b699a3690a0867eae64202cb446e4a8086a774d4682e07b24b4ea679937794541129094508ab4a4c5de3e99878dac8c54989c3000002c44d008000057a5bdadf85a26cf4de8e8d4b856730f867c00000020480007900003f72ba12a262452987e14e40003b800010e800046401ad4dc67f00025f8520652136007400065e0d19240d4800021c0810f6a2774dd1580e5c38c4f9284cfae00
  | 21 => 0x33932a847a452b2250c208d092749a9398c047923e198b0ec22c605025d05080d215a163837e1f459e2d507a25952c2ab753400170540d6099628804988080840e222c800082a0004c7914037a00028b9b985de8d442e13740001e9000196cf3c00424a288c0003741e013ec47a42e078800102e05743e13d827075a311191ca7c26926b1a5d04c4d0000000048473b4f10d88034552449a3bc0002cc389a3680000002950000fe67585221c55354b56489052d62682d354079853a11b2c984540c62311758c00f300450001a750f67a83dca5d88de86e0002a147166df0000e183ae2830000ed80000000001194b7e0000002c400008b700018940000000002bbc00000059786d00000002d59a6125e3950002a484287ab000140880a743343252041472a104a2904a44bc072a72d642216463808ccae6fb0d215cd23661b217882cb36ade03009714169cc0001bb4000000000237d6ce7ad00001580007dc32a9420bca00000f2d88c980001fc8000b967741768000000a4b3dd2bcc2e479700026386342e8000000062480b4a81ba8bd0ac211413acf102e93c48e0c05e480539a1f40bc0353c08eb46da6cd0c58614dae7e505b801cbea72827e2009370356379a0f846403039e8644338b4e427abad3e28842fe80c493090a461059151a42b55c8be4a468713ce02340003ed4e18d3800000043100013ae00033985d079690426c08655fe7ce2b30000b903334ab2934ad82e606888787681884ea81a8b823a400000000002c017ba7f82d63c441fa2a41f860b189ac1c174000000240800014a4f4800148e5db2e900011ca4a70000dcd6a038e3ca9bc558e00000027bc4f05ff2abac0886e43608405a40e03b132b0000fce5d83c8830d38400000016a4000a5434f16745882403ec83b0e10a39082000000053809f9344fa200025b8070b6c3dd11b181c1848410239b44af042247506c92c2a691c78000000a3f50a27a845a4d40e98b2456eb3256b2dacbf045425a266d5fa9f40001c70000000000044ce6243302aaaf00005e304e98343a040000000010309b51b7000000052249180011a40002f6800000000000027a00007023848000da85684438e815041c12288000c4c7842f0283853e93900004f868e4103a5a4c815aad43c6924d5f200000000003500001b6159013e3ac178080414c6b8135134864e7dd35715f91028212468000000b2638280000f65e1271a8f802a5d00001f187024480000000000000235a7cc8e800000027e9200000000293c00000057b00011c44e83e69270272ab500018e91284611a8800000000027823f0af228c2dc00002a06422dd91a83a84c60378000000366236000000077f313ade521e03e09da6bcd86000000000059c3382a69dcc15c73e20b0000b9e0004ad8000b6a5be43c12e8f2012c315ab
  | 22 => 0x1412dc0a213c999d12c6c023e000001a36300000008bc63650797655dc71b2ad03a52bc32b000290963c3fa38a2208710222160acf4268ae54a3a2c82da85432e0abcf6e785200a77d2022f44eb2b64a3a1dc37921dc000b580002a3800000000014a14f2b384770dc916880c185190ca9400050f9ebc96a1fc5228a0469e5f60130da883c4d756611911404f141c10343d00185061255686067133ad5413c1e2108a03525246254328dc7e40940ff1220f446fe0c1016102a6235252b6c75e86d427239d0987d222a97893385624c818e4cf04424b90fdcb8435c5ad27d86184a631b9cbd2a4000331111c7309be31a23991ac5aa1d82dbc000ad0020000055c1bb00029dc8da6680daa0014c2b3e1c496503fa3c60002e1400000037f80010ac6444a2800000008c00009940007e00000ad4d8a0004d418cd084000000261c00002e451800000084d58e25f4aa231e4b4a71029016a0981c49514b5c0d280004f661002e0f5c00011e00000000009c530b2634420b6801e9df08ce50700000003ea6704fc97e90360b820e8d6ca786112a700000004fe000086c0000000000000a06000197a0f0fc81c6063800000000053680000009e12e897a94921a918a26b40005050001af4430828081832078ab5e087aaac81659a1bf1484bbe4ea32692c40b675500008851f64754d129480007bb14b296c0007d531da0580008be1828bed58a4960001fd4530ace38180012260b503b0dad0d82a60c4963052264803082ac14e74500017a41040eb46c946d21a000178939169e1c825014584189cd447105161815d0002330a883682ff1388f7c29b0001ad968811a156160926098b00000000007a32b28001052000245a2940005d300024f4000000000000063889100013640000004158000fb48f80000ef4fe49e63b200944682d4374a9acf8a28e325182011ca642749d6c3089d3039a8d0fde2c318315600007371ffa1d8cfc3502a301e40000d02f3862966e00000000002c2000218ae200000000d31fd8ece1290c81d796e810b59d02f486a9a602e8000fd43f8019000000000a00022b4d0400012f89842a68e950501901ce0002d68508e560001f986853da8fa26f9b04d5a0002eb25dd69660a0699554b388454a1000000090c45313952987c83ff11eca6a110344a50c486a6f25280009809d2129a5e08e200049a2c3c7e2000067aa8d07453d1bd014818244b38d0e1c0988862392a9944851452f8b352e668c50d05694a27e938b1368ddc4300670600a925613281e7c1bab3308087e81f60a344c09b865401434a85e415433231714c93229210c71a807563215b82494302b121031658954a280be87ec8108f70002684000940134114c47000e0f5000107673a17625e80006d354021811962b2000000035a62f3bd89186aa02800416782b83
  | 23 => 0x1455a912cc00004a0a48000bf23cc4921a14ee413c0cb9a440000e139900001161e14b12ce401683118580007ec51e11e13284deb03287144568285e3638b684c62070002a4c9882e700020e4de06f72861af91920850001a7d3d868106699f10923e9041812c886a3a2108fbd1200000001ac901093300029b09464ce2928d3043405119117b143c0005c1000115e9d120d063c49e16e58319d0fc40bc22b2b6874c4974d380004b217b4539e50f005a716c09d8f84af503faad02443785ac8268b8e8092b68270ed212e25f8cf0d6a2de287a6244405b221616947220e808717c447e4f300826310ca000500ad00c300003fd854959a0000eb0c1041c5a21a9a8f157c3ea4798258e98b53444997cd1e00023b2c9c9643bb15c2a880009d01f5abec7c2a2e000121400066506fa2b852ab6442a9a9c6ae3d60831b086620953181ab125842011505f879428d3bb144c00078a5148000dce52f0001a0c4f800028327d477e0a444f9be00dc8ac15e86a8f2c9175c399d516a00509200000008bf34d2da457ca8f2e2066ca0259042b9b2533e2f321d98054b44ee57e14b0b741315a60bf88f22172fd927d6482485ae8000c329d94080d794426fd0ac05891066dc582000545e3a1000000000048c00015d40002a10001a941f40001fd99903960000000000000641000101c224000000116d3bc844000200ca827045970e34c426900002360d42434570a8c4f7e9864d90001094000000000029e54f29d0a3ce8429339829a12c80000a7000136600023980000004c700008e40003be26a8000dd6000000000000000012b000009e8360001c9d40802400020645565b138f1ff0eea0002ba196824000000001f800000052400011e887e077000138c000000000000000053a8b7400012542d94e406857c0001f5169a612000085513ab7a23b9514b3000000000016120000001fc000000030d17d00005fc0ee8fd15805843f5851c00000058c00000006493b10b5462e76f59009113300cb00c8000b921552090000a90b651490264baaa9820ca470e883e53d988a4e1a95c3740000a124895208fc00005125721c2cbdc24b43497341fc16c4688a6416677149e2ba94ac0f73549124a66ae72e29980e1e041598907c37c2bc371823c10e6711d91a88000a6a05798f515600050b8ac400059221f217c000666503a2a87fa63130e024884a2474199a9920a2fd0b8031501c072521a22c4fa00048fa0bc59e91e0000000b6e74608fab180000782ab10b489852044e2adca527fd27fa6dd2e231f139ab2023a00000002294a01561ee00000003db49b80011e400048194ec0000004e0800136203958d93255108fd20c076d6f0b0b0cf19840000f022296200004ad0001490494000513071d1143452d80aec60e49e2aa11012168471b4944095c8db17c0
  | 24 => 0x34a1beaa9c20e12a054a65082e0ea15faa1c9de0980000f551886323ce88d55540d506d000081c4240000a18f4ea9139f89d561a76602221980007d84230000adc0c40bb036d4c412d53f28c0ad2a1800007117022d730b8e6853c57f25d961cb1ea2a01c03d42ee83754caa7d358b7c3d0941087e57003480451b86cc2c01de03cab610f39824ef29b44d826115e89140849c887384f92c8a1a86ee54313116f0f648ed18a8c082428b8595170cd14b003b625180e215151b0e9479c0c033c9f3d2b0a100c6110479e57107cacb05b83280c30ba90b478c2232380474000261aaf400068026286d931419257ba3e40007e854ba4680000060001f1ceca1462a9800126c6f65618f3400083d00023850a22ff0002c551628721701e180008dd00024acbae00014e0e589e47f93db194466c81a0f6299936c5501d42e10b463645a51b1166094124d20a94322fc2802c889367470ea9d24f8066b0860960f4c6fa1cf1ae475c3bc3b587795343674510aa40f82640a62b4403e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa4d8510d620c0015930021ac41800385591539843000722a9ac53086000a5583152610c0014e3002a4c21800295e1953584300070b322a6b086000e156454d610c001c8aa7312c2180039154d62584300052ac18a8b086000a7180151610c0014a908a9ac21800295e0153584300052bc2e86b086000a558510d610c0015a30021ac2180030799173d40300060eb22e7a806000c4d7398b500c00189ae6b16a018003155ce61d40300062ab9ac3a806000c1d75593300c00189aeab166018003155d561cc0300070cb22a7180600085f865d5300c00123908baa6018003075d5644c03000626baac49806000c5575585300c0010bb063aac990002956066354f200042ec1cebb24400085f835da548800307908bb2a710002876106354e200052ac08c6a9c400085d839d76448001898eca9a64900029560c54d852000538c00a9b0a4000c35755d061480010eb0e2a0c2900029560c541852000538c00a830a4000c95745cc614800158b07210c2900039154d321852000658ba2e030a4000cd1735c061480018aae7b0ea090003155cc61d41200042ec18eab204000a1d831d564080010bf0cb98a8100070799173150200060eb22e62a04001c3a645c05408001872c8b80a8100021761c5498c200052cc00a9318400085d8715163080014b3002a2c6100029560c549842000538c00a93084000a558315161080014e3002a2c2100032a591700842000664b1ae0108400085d839d6600800183cc8b9ea0100030759173d40200042ec3cc7a80400085d8758f50080018aae730ea010003155cd61d402000652b20e29004000cc5631c520080010bb063aac9880029360a6354f100042ec1cebb24200085f835da548400307908bb2a708002876106354e1000526c10c6a9c200085d839d762840019c6c4b80430800278a1f21482100042ec1cebb222000a4d8315362440014d3002a6c4880030b5d5741891000436c38a83122000a4d8315062440014d3002a0c488003235d1731891000654ba2e03122000cc9735c062440019c2e2b80c488003315cc62905100062a3b2a698a2000e4553189314400189ae7b16a088003135cc62d411000571434431022000ce07648520440010bb07b82ca080021760c75590100050ec18eab202001879805d854040010bf0cb98a8080070799173150100060eb22e62a02001c3a645c05404001872c8b80a8080021761c5498c100052cc00a9318200085d8715163040014b3002a2c6080029360c549881000534c00a93102000a4d8315162040014d3002a2c4080032c591700841000668b1ae01082000ce1625c021040010bb073acc0080030799173d40100060eb22e7a80200085d8798f50040010bb0eb1ea008003135ce62d401000626b9ac5a802000ca5641c9100400198ac639220080023921d6244010
  | 1 => 0xb0d39843a800217e1d63087500042ec3ac610ea000c1e7458c21d400183ae8b1843a80039158d21087500062cb1ce010ea000c59635c021d4001ac242b8043a80070710d731915000e0fa02e6322a001c5a405cc64540038b280b98c8a800217e1d6318d500050e422c631aa000a1d8319243540014390ca1886a80070e1917010d500062db1ae021aa000d19435c043540010bb063b284a80021760c7650550006b090ae010aa001c1e645cc54140034390ca9a87a00021760c7558b400042ec18eab0e8000c59739c26590001273003a2a7200025660f76542400052cc00ebb1a800085e87153635000189aeab90c6a0003155d57118d4000662b92e231a8000cc9725c063500019a2e2b80c6a0002936086354d400052ac08c6a9a8000a1c8654d43500010b90cb9ea0a00021761c63d41400048ec18e8a828000c1c7418d5050001633063a2a0a0002ca608745414000598c08e8a828000c5876d8d50500018b0ec31aa0a000346dcf435414000598c0e84a828000b2982d05505000343908baac620007071d16354c4000d16422a6b108001a348454d61100010bb0f31ea0200021761d63d404000626b9cc5a808000c4d7358b50100018aae730ea020003155cd61d40400061dbb2a0a008000e19635414010001c52c4a8280200038c585505004000e1d2a6eca008001e1a5458d40100030f70cb80a998006872116550f300062ab2ae39966000c4d655cb31cc0030bf0cb98a918002176187454e30004acc00e8a9c6000c1c74d91538c0018aaa7b8ac5180031354f72586300058c422a720460009588754d408c00383b063a2ca980070ba08745953000e16c10e8b2a6001c36811d1654c00386b023a2ca980070e60074595300060e3a6e6b2a600085d839d7644c0010bf06bb4a89800307d91731513000e0e322e62a26000c3b645c0544c003870c8b80a89800217e1d6590d3000d0e422cb21a600185c87595434c00343908b2a86980028721165cc9300062ab2ae39926000a1c84595324c00143908b2e62980031359572cc5300050e422ca98a600183c845d9504c00347108b2c80980061e21d65501300064c3b286a026000e196550d404c00143908b2c609800287614735903000c2ec1aec2a06001c1e645cc540c00183ac8b98a8180070e99170150300061cb22e02a06000959801d1530c00149b05b22a618002956076454c300050ec34c8a98600085c87591530c001838e8b22a61800307dd96454c300060e43ac8a986000c1d64dc1530c0010bb0dbae861800307dd564d0c300060ebaac82186000c99645c0430c001c1ac8a9cc4180029360c549883000534c00a93106000a4f8654d620c001c1cc8a9ac41800383591535883000526c18a8b106000a6980151620c00149908a9ac41800293e01535883000527c2e86b106000
  | 2 => 0xd72181310042ec18eab26420085d839d660c84010bb063aac9108021760e75982210042ec18eab224200a4d8298d53484014ab0331aa6908021760f70594210042ec18eab204200879801d5640840143b063aac8108028e60075590210042fc32e62a04201c1e645cc540840183ac8b98a8108021ee19701502100e1d322e02a04200c39645c054084010bb0e2a4c610802966005498c210042ec38a8b184200a5980151630840149f0ca9a641080383591534c82100712b2a84a084200e856350941084014af0ca9a621080385591534c42100742b226498842009c583dd12108401c4acab224210802996185448421005a2c18a89084200b61801512108401d0ac8b1a4210803515cd5348421004d2c20e090842009c5831c121084010bb073acc0108029660e75980210043cc38a93004200a598315260084015c10090ac01080398995215802100730b2a42b004200ea2644856008401d42c890ac010803b098d215802100760b1a42b004200a59839d560084010f30e2a2c0108029660c545802100564c1c84b004200ae18190960084015c303192c0108039254d325802100568c1c82b004200ae1829056008401d4284a0ac010802b860a315802100728a9a62b004200ec1324c560084015c10e90ac010803989d5215802100730baa42b004200ae38448560084015c30890ac010803989512158021007302a242b004200ae38348560084015c30690ac01080398d4d215802100730a9a42b00420085d869cc54d40010bb0e2a4c7a800293a085458f5000526c10a8b1ea000a568115163d40014ab022a2c7a800296a005458f500042ec34e6296a00085d869cc51d4003874c8b80c9a8002966006498f500042f43ec8b1ea000a4e8219163d400149b04322c7a800295a046458f500052ac08c8b1ea000a598019163d400183ae83a2c7a800293a087458f5000526c10e8b1ea000a56811d163d40014ab023a2c7a8002966007458f500052b40ee4b1ea000a5581dc963d400143d09392c7a8002876127258f5000527416e2b1ea000a4d82dc563d400143d0938ac7a8002876127158f500050fc22e0b1ea000a1c845c163d40010bf0eb18c7a8006872116350f5000626b1ce421ea000c4d635c843d40018aac738887a80031558d7110f500062cb1ce021ea000c59635c043d4001a3286b8087a80031558e71d8b500062ab1ae3b16a000c55639c742d40018aac6b8e85a80021760e7690b500042ec34e7216a00085f8758e42d40010bb0eb1c85a80021760c7650b500062ab1ce3996a000c55635c732d400189ac7396c3a80031358d72d875000626b1ce5a0ea000c4d635cb41d40010bb073b483a80021761a73907500042fc3ac720ea00085d8758e41d40010bb063b283a80031358e72cc75000626b1ae598ea00085d839d821d40010b
  | 3 => 0x322a601c3b425c06454c0387682b80c8a98070e991701505300e8c21ae02a28600939801d15350c01333003a2a6a1802c66007454d430048f430e8a9a8601c1e861d15350c03a1d043a2a6a1807436087454d4300e8b408e8a9a8601d15811d15350c03a35003a2a6a1802476007454d4300e8cc00e8a9a8600919801d15350c010bd0db82a6a18028721153d89430062aa9ae3b128600a1c8454f6150c0189aa6b96c2a180287211531814300626a9ae43028600c55535c46050c0143b0da9a862180307dd95350c4300e0f2a6eca188601a1c845954310c0183eedbaa862180307dd96550c4300742a1ac4b088600e1a6550d6010c01c32caa1ac021803a250e625804300744a1ac4b008600e91439856010c01d2286b0ac0218068e21175580430070da9a86b008600e195350d6010c03c34a8a1ac0218078615143580430070dc2a86b008600e188550d6010c01c34eaa1ac021803865d5435804300e1d322e02a0a40085d8715263148014b3002a4c629002936085458c520052cc00a8b18a401c1c7458d53d080346908a9ac3a10021760e75983420042ec1ee0b2c8400a598015263908018aaeab8cc721002966005458e420052ac0cc6a9c840085d839d660908010bf06b86caa1003135cd72195420042ec1ced2a28400939801d1535080385ca9bb284210021760e7598042004acc00e8a9e6400a5581d9153cc8010b90eb22a799003071d16454f320064cb22e021e6400a558315261cc8014e3002a4c3990029560c545873200538c00a8b0e6400a548454d61cc8014af00a9ac39900295e1743587320052ac2886b0e6400ad18010d61cc80383cc8b98a91900307591731523200e1d322e02a46400c39645c0548c8012b3003a2a6990021721d6454d320060e3a2c8a9a640094f8754e424c80161908a9a84990035154e71cc9320060eba2a63026400c55535c4604c803874c8b80a8288021761c5498c510052cc00a9318a200a558115163144014b3002a2c628807071d16354f4100d16422a6b16820085d839d660d04010bb07b82cb20802966005498e4100626baae531c8200a5980151639040149b0531aa7208021760e75982410042fc1ae1b2a8200c55735c465504010bb073b4a8a08024e6007454d4100e1b2a6eca08820085d839d660104012b3003a2a7988029360b6454f310042e43ac8a9e6200c1c7459153cc401932c8b8087988029360c5498b3100534c00a93166200a4d8315162cc4014d3002a2c598802932115358b3100527c02a6b166200a4f85d0d62cc40149b0a21ac598802b26004358b3100e0f322e62a46200c1d645cc548c403874c8b80a9188030e5917015231004acc00e8a9a620085c87591534c401838e8b22a69880255e1d53905310058a422a6a0a6200d45539cb314c40183ae8a98c0988031354
  | 4 => 0xcac89408a4c0c285c1fa670dd97e0004780006a26a000000f6298000e880044a7f0001d3114274c08000ba8001416c01e1a03b96f1322406d8240a20dc951513b00344093935a76417a092f213c5a0c9262354f00203c45d8471a407c860378bc3ec4c91081d2dc000599114107b0508ed492000520723fc045188e90002306a0004a2910308000428783a1b145a0e02ca3727430c9c19d4b063c4399a35e928000001a414c0000000000105014306834f193d1a241d010fb46a51ca194f1ea8bc908420ae000011902c63946b0c11441ed0e950000600000003cc41520807000514001eb1e08484e1530000c9098ad0147003005a202000b5941428000000000940011400014e460310690d83acd58a51640003d11d076020001db3a40010e2042f60e8aa80b4780a8001e4000000761dc48c628831f0322254002294180b88b1e70002e41590a392001150e21047b82717d22a218000c53401f85c03d0006a8730000f8334869343f2470498000000002d9970008c8221f51b208c001a30dc0002195d0002251f254358890fc19542a5a4cf8df2481311ca2e0440000003c38a4cc6395a27e8d0551892500fcefa3809a3f8eb8cc00e04800010080b0000d01c000020080e018000400800022018400200000800140060905401014008000a81601010008021e01e03006020000b00003800000000280200000020200181c0602c00006008040e83a01800028000b800030060080a018000303602008018000182601000020180481c0080200818218000401a0080e000020101a0000c0f81802014058000082a0083e00004000000501c020000980c0000e0003806808079100000402086000020180006006038080000c000020303c0080023000070100000006800008020980209808030020480000802018000205400802010100280010012008021c80e01004008220301a0000789951625845400f0d2a2c6b00a801e2a545896015003c64a8b0ac02a00296a0e75580540052cc1ceab00a800a5681dc963150014ab03b92c62a00687a127258c5400527416e2b18a800a4d82dc5631500343d0938ac62a006872117058c5400d0f420e0b18a800a4e821c1631500149b04382c62a00295a047058c540052ac08e0b18a801a38845cd60150034750839ac02a0029aa08735805400534c10e6b00a800a72811cd60150014e30239ac02a0029ce0572580540053840ae4b00a801a3a841c960150014b506392c02a0029660c725805400539408e4b00a800a71811c960150014d704b8ac02a0029a209715805400d1d420e2b00a800a5a831c560150014b30638ac02a0029aa08715805400534c10e2b00a801c1e645cc64d4c03838c8b9cc8a98070e10170191530062dc1ae0322a600c58835c06454c0387686b80c8a98071690d701915300e2ca1ae
  | 5 => 0xb94e3ac610f481804e318f080031a124880660002e9271cb4207748d9b4332078ae1bc1365c4ba00400c6f87910c11a000601d53820c04f1b70003e04c003002739200b700085c00160000609290001c20006f00033c00000058000000c987500034cdc1a600061c3c1e544e00000000000000d811712e560240634743d00000047e688a40910000000023d038000961120e22b9298ff2165f1182220f240000161316000001ef0be740af8ef3f6269198ce4226a4e216800035cb81c803e2a05784628828c948310ca728000b10007085492b0667f48f91425e5fc2b09f2320a4f693e4aa87c840ca026064071f2440380081bf03470cad9a8276220f51263f4480f41bd1846390b0851ba0003381b2bc0004902d000814ed2503307cc96a2638e3f0f892e16c8b09b08f000000798a640e368b50ea3e8518620640820003587d0ec014cb2062a41cd210b5364804739750001780021b17c5902a1922e6001219b346c6507c8b0100000558d81d020c00000000534bb95602a55caa1422941c12b00039e88c000e436a8ecbc000318618d29040000001a0f102c000000001ee000e69a73bc3b86400008052c9112331059c7d10f49032c8119b372341019c648a370ff8ac21c00127a1900095c0000006a5989296d41e4f0e60094342580001208e44c6782c04a524b924b4984dcbd20e3ee148420360a012d2680017e588d091a2122ec001ba14040ca01b611649c3f86d0002f40022b000154ea00000082c061ae48e5941300007238
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x81600b0d00a4e0f1c54ba3509c2240464d9f0a4c0263a50d003c04600448448314950120c440103000007000502804800c44000002c100512648835c06454c014519120d701915300606259801d15350c012199021153d894300505251535c76250c012199021153d854300503251535cb6150c0121990211531814300503251535c86050c014149454d7118143004862617550d6010c01419901d16454f32004946408454d61cc801419901d16454d32004c26408454d424c801419901d16454f31004926408454d62cc401419901d16454d31004c46408454d414c4012a1942012158021004b064c8048560084012a19421d2158021004b064c874856008401641939d52158021004b064f8448560084014619715121580210059064c544856008401a418354d2158021006065d1801d163d4001c4163485700875000506259435c04354001419901d36454e30004866588454e408c0014149459571cc93000503251655cb314c0034189759543501300050664087591530c001249902115358830004946408454d610c00101c985d5644c0300050325175589300c001414945d5614c030
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x28200990000801404d112cc00e8a9a8600a04684966007454d43004823404a2a6b8ec4a1802409a0251535cb6150c01204d0128a9ae430286009046809454d7118143
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 66
  | 6 => 1666
  | 5 => 2953
  | 4 => 601
  | 3 => 42
  | 2 => 6
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
  | 7 => packedAt gbK7 (1870+((h/22+packedAt gbK7 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 6 => packedAt gbK6 (68302+((h/555+packedAt gbK6 (61642+(h % 555)*12) 12) % 2200)*12) 12
  | 5 => packedAt gbK5 (153552+((h/984+packedAt gbK5 (141744+(h % 984)*12) 12) % 3544)*13) 13
  | 4 => packedAt gbK4 (37459+((h/200+packedAt gbK4 (35459+(h % 200)*10) 10) % 722)*11) 11
  | 3 => packedAt gbK3 (3024+((h/14+packedAt gbK3 (2940+(h % 14)*6) 6) % 51)*7) 7
  | 2 => packedAt gbK2 (494+((h/2+packedAt gbK2 (486+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff83fc30c3818fff07fff80ffc043cf00f3cf
  | 1 => 0x783fc3fc0fc01f1c3f8783ff07d18d33334d33
  | 2 => 0x803ffc3ff0001fe03ff803fff8260e3cc38e3c
  | 3 => 0xffc0003fffffe0003ffffc0000380fc0fc0fc0
  | 4 => 0x3fffffffffc0000000003ff000fff000
  | 5 => 0xffffffc00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10480440000800260008a08042004045001045
  | 1 => 0x2a1242940e4149089485092a05918512314512
  | 2 => 0x8424a82b9002924129501254b0260a28c28a28
  | 3 => 0xce86220da694c0003e66580610b80f80540f80
  | 4 => 0x3249231c918000001821029000abe000
  | 5 => 0x773f3300820400020c446060c63d6fff000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffffeae8ffeaeae8ffffeae8ffeaeae8ffffeae8ffeaeae8ffffeae8ffeaeae8ffffeae8ffeaeae8ffffeae8ffeaeae8ffffeae8ffeaeae8ffffeae8ffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14472
namespace PEqualNP.Outside.L_meta_14472
open PEqualNP.Outside.L_meta_14472.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 42 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_576 : Interval gbAtlas 4 576 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 601 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 (concat bgb_4_384 bgb_4_416))) (concat (concat bgb_4_448 bgb_4_480) (concat bgb_4_512 (concat bgb_4_544 bgb_4_576)))))
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
theorem bgb_5_2944 : Interval gbAtlas 5 2944 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2953 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))))) (concat (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)))) (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))))) (concat (concat (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752))) (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)))))))
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
theorem bgb_6_1664 : Interval gbAtlas 6 1664 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1666 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 66 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffeae8ffeaeae8fffffffcfffefffcffffeae8ffeaeae8ffffffffffffffffffffeae8ffeaeae8fffffffcfffefffcffffeae8ffeaeae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,64,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,64,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_14472.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,6]⟩,⟨.or,[0,1]⟩,⟨.or,[9,4]⟩,⟨.or,[6,7]⟩,⟨.and,[10,11]⟩,⟨.or,[1,2]⟩,⟨.or,[13,7]⟩,⟨.and,[14,5]⟩,⟨.and,[0,4]⟩,⟨.or,[8,12]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_14472

open PEqualNP.Outside.L_meta_14472 in
theorem PEqualNP.Outside.L_meta_14472 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
